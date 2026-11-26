# Fixed-cap controlled-window concavity for actual quitting profiles

This is a necessary condition on actual global minima, not a uniform
equilibrium theorem. It gives a raw-matrix certificate excluding complete
finite-window modes, with an exact M14 example and an open neighborhood of
raw tables. All comparisons use independent private strategies and full
behavioral response caps. It does not replace an inherited semantic endpoint
by an actual profile, and it makes no assertion about sparse owner supports.

## Exact statement and semantic definitions

A complete stopping law is a probability law on the nonnegative integers
and Never. Players' laws are independent. The earliest finite date absorbs,
with quitter coalition consisting of all players choosing that date; if no
finite date occurs the native payoff is zero. Write U_i for prescribed
expected payoff, B_i for the supremum over every private behavioral
replacement of player i, and e_i for the payoff of its pure Never response.
Let d_i=B_i-U_i, let N_i be marginal Never mass, and put nu=prod_i N_i.
ALL-END means B_i=e_i for every i. The observer carrier consists of profiles
with d_i=0 for all i!=p. A global minimum means a profile minimizing J_r on
this carrier (or on a larger semantic carrier containing all such actual
profiles). Only the actual branch of such a minimum is considered here.
The hazards at a date are conditional quitting probabilities given that
player's own clock has survived; positive Never masses make these defined
at every finite date.

Either the raw matrix certificate below or the explicit premium-ray
frequency certificate in Section 8A implies the complete controlled-window exclusion
in Section 2, with the fully specified independent variation constructed in
Sections 3--6. The local-minimum statement uses the Euclidean topology on
the finitely many window hazards; those variations also converge in full
marginal stopping-law total variation. All quantifiers in Section 2 are
for each fixed raw table, r, N and S; epsilon is independent of the particular
profile or the strict margins inside its qualifying window.

## Conjecture-facing change and strategic inputs

The actual four-owner infinite-support arm of the four-player minimum
reduction permits exact ALL-END observer-optimal tails, including fully
mixed tails. Local contact feasibility does not exclude that arm. This
result imposes a genuinely stronger condition on every actual minimum:
late full-support windows satisfying the finite rank test cannot have all
the marked pivot comparisons strict. For the explicit raw example below,
an eventual full-support, eventually strict-Never pivot tail is completely
excluded, throughout the unbounded premium family M>=14 of Section 8A.
Such eventual full-support minima must also have geometric remaining-mass
decay, as proved in Section 8A. At M14, Section 8B strengthens this to zero
upper Banach density of strict pivot dates in any eventual full-support actual minimum. Tied pivot dates
in the same fixed window can be retained exactly; there is no claim that the entire four-owner arm is eliminated.

The actual incoming minimum and its finite hazards are the object being
excluded, not an assumed strategy producer for an existence theorem. Every
additional strategic witness needed for the contradiction is constructed
here: the exact finite constraint fiber, a strict descent along it, the
independent hazard implementation, and the full-cap-preserving head splice.
No separately supplied continuation, rate schedule, tail approximation,
controller, or correction oracle is required. The existing continuation is
kept literally unchanged. No minimum-realization theorem is claimed; an
inherited point without an actual representative stays outside the claim.

## 1. Raw data and certificate

There are n>=2 players and a selected pivot p. Native own-singleton and
Never rewards are zero; every other absorbing reward Z_i(D) is finite.
For distinct i,j define

    Gamma_ij=Z_i({j}),       J_ij=Z_i({i,j}),
    Gamma_ii=J_ii=0.

Thus Gamma records singleton rewards and J participant pair rewards. For
i not in {j,k}, put T_i,jk=Z_i({j,k}), the passive pair reward. Assume
Gamma and J are invertible. Put

    v=Gamma^-1 e_p,       w^T=1^T Gamma^-1,
    A=I-J^-1 Gamma,       b=J^-1 e_p.

No entrywise sign of v or w is assumed. For symmetric P define

    Q(P)=[P Gamma^-1 J+J^T Gamma^-T P-P]/2.

Define the symmetric matrix K by K_ii=0 and

    K_jk=[w_j J_jk+w_k J_kj-1
                    +sum_(i notin{j,k}) w_i T_i,jk]/2, j!=k.       (1)

The raw energy certificate is a pair of symmetric matrices PD,PV satisfying

    PD v=e_p,       PV v=w_p e_p,
    QD=Q(PD)>0,     QV=Q(PV)-K>0,                                 (2)

where >0 means positive definite. These are finite real linear equalities
and strict matrix inequalities. No reward on a coalition of size at least
three enters them. All such rewards may be arbitrary fixed finite numbers.

Fix a window length N and a set S subset{0,...,N-1}. The finite control test is

    |S|>=n+1,
    rank R_S=n,   R_S=[A^(N-1-k)b : k in S].                       (3)

All data in (1)--(3) come directly from the raw table and a finite date set.

## 2. The controlled-window exclusion

Fix a raw table satisfying (2), or belonging to the four-player family
proved in Section 8A; fix a pair (N,S) satisfying (3), and r>=0.
There is epsilon>0 with the following property. Consider an actual
independent-clock profile which is ALL-END, has zero debt for every player
other than p, and has strictly positive marginal Never masses. Suppose a
window of N consecutive physical dates has all n hazards in (0,epsilon).
At every date in S the pivot must strictly prefer Never to immediate Quit.
Other pivot dates may be strict or tied. Suppose the continuation after the
window has all Never payoffs and its prescribed pivot payoff of absolute
value at most epsilon, and its joint Never mass differs from one by at most
epsilon. Then the profile is not a local minimum of

    J_r=d_p+r nu

on the full zero-observer-debt carrier.

The improving variation changes only these N hazard vectors. It fixes all
n entrance Never payoffs and all n entrance full caps, so all earlier full
caps are preserved. It retains observer optimality and every tied pivot
comparison. There is no nonuniform horizon limit in this finite variation.

Consequently, for an actual global minimum with positive Never masses,
every sufficiently late full-support window of this fixed pattern must
have at least one pivot contact at a marked date in S. The sufficiently-late
threshold may depend on N,S,r and the raw table. There is no assertion
uniform over growing window lengths, and empty physical dates are not
silently deleted.

## 3. Exact finite-window maps and the full behavioral splice

For a root hazard vector q, let H_i(q)=prod_(j!=i)(1-q_j). The passive and
Quit offers are the exact multilinear polynomials

    P_i(q)=sum_(nonempty D subset I\{i})
                  Z_i(D) prod_(j in D)q_j prod_(j notin D,i)(1-q_j),
    Q_i(q)=sum_(D subset I\{i})
              Z_i(D union{i}) prod_(j in D)q_j prod_(j notin D,i)(1-q_j).

Own-singleton zero removes the constant term of Q_i. The linear terms of
P_i and Q_i are Gamma_i q and J_i q, respectively.

The continuation after the window stays fixed. Denote its Never payoffs by
e_i^+, its prescribed pivot payoff by u_p^+, and its joint Never mass by
nu^+. Conditioning independent clocks on their survival preserves their
independence. The conditional tail inherits ALL-END: any tail response
strictly better than Never could be grafted after pure Never up to the cut,
with its positive opponent-survival multiplier, contradicting whole-profile
ALL-END. Its observers also have zero debt: following the prescribed head
and then a better conditional response would gain the positive joint-survival
multiplier times that tail debt. Thus its full caps equal e_i^+, and each
observer's prescribed payoff equals e_i^+. For window hazards q_k,
k=0,...,N-1, recurse
backwards from e_i,N=e_i^+ and u_p,N=u_p^+:

    e_i,k=P_i(q_k)+H_i(q_k)e_i,k+1,
    u_p,k=q_pk Q_p(q_k)
            +(1-q_pk)[P_p(q_k)+H_p(q_k)u_p,k+1].                  (4)

These are the literal Never payoffs and the actual prescribed pivot payoff.
Set c(q)=prod_(k,i)(1-q_ik), and G_i,k=Q_i(q_k)-e_i,k.

Impose the following exact constraints:

- G_i,k=0 for all observers i!=p and all window dates k;
- e_i,0 is fixed at its original value for every player i;
- G_p,k is fixed at its original value for every k outside S.

There are nN-|S|+n scalar constraints. In particular every originally tied
pivot date outside S stays exactly tied; a strictly negative original gap
outside S may also be held fixed. All marked pivot gaps remain negative
under a sufficiently small open perturbation.

These constraints hold at the original profile. For an active observer,
zero debt means immediate Quit and Continue-to-Never are both maximizers,
so its contact equation is exact. Conversely, the observer contact equations
and the unchanged continuation give full caps e_i,k by backwards induction;
the prescribed observer payoff equals e_i,k as well. For the pivot, every
G_p,k<=0 is retained, so its full cap is e_p,k. Thus fixing entrance Never
payoffs also fixes entrance full caps, not just a finite subset of responses.

The unchanged head sees exactly the same continuation caps. Its old pure
Quit dates retain their values. All responses that enter the window are
bounded by its unchanged entrance cap, and Never still attains that cap.
Every earlier full cap is therefore unchanged. The unchanged observer
head law and the altered window law remain optimal.

This prices all private behavioral deviations. Along the unique live
history, conditional on its private random bits, a deviating player chooses
one deterministic quitting date or Never. Every such response is covered
by the backwards comparisons and the unchanged continuation's full cap;
averaging cannot improve it. The prescribed hazards are independent private
Bernoulli choices. No public coin, correlated recommendation, or continuation
placed after infinitely many dates is used.

Let s>0 be the joint survival probability of the unchanged head before the
window. Since the full pivot cap is unchanged, the change in the complete
objective is s times the change in

    F(q)=-u_p,0(q)+r nu^+ c(q).                                  (5)

Positive marginal Never masses imply s>0. It remains to exclude a local
constrained minimum of this smooth finite-dimensional objective.

## 4. Linear contacts, rank and the exact fiber

At zero hazards and zero continuation values, with nu^+=1, write a_k for a
signed hazard direction and f_k=sum_(m>=k) a_m. The linear contact equations
for observers and the fixed entrance values say

    f_0=f_N=0,    Gamma f_k-J a_k=g_k e_p.                        (6)

Indeed the derivative of e_i,k is Gamma_i f_k, and the derivative of Q_i is
J_i a_k. The additional fixed pivot gaps say g_k=0 outside S. Since
f_(k+1)=f_k-a_k, (6) is exactly the controlled recurrence

    f_(k+1)=A f_k+b g_k,    f_0=f_N=0.                           (7)

Eliminating the states gives R_S(g_k:k in S)=0. Hence the tangent space is
naturally ker R_S and has dimension |S|-n>0. The full constraint derivative
has rank nN-|S|+n by (3). One way to see row independence is to solve (7)
forward from f_0=0: the |S| free controls parametrize every solution of the
contact and initial constraints, and the n terminal equations have exactly
the rank of R_S. The correspondence between f_k and a_k=f_k-f_(k+1) is
injective with both endpoints zero.

Choose any nonzero full-rank minor of this constraint matrix. It stays
nonzero near the zero data. The implicit function theorem gives a smooth
exact constraint fiber of positive dimension through every original window
in that neighborhood. Its first and second derivatives are uniformly bounded
on a smaller neighborhood, using this fixed minor. Every original hazard
is positive and below one, and every marked pivot gap is strict. Thus an
open two-sided neighborhood in the fiber is feasible. Its size may depend
on the original strict margins; no uniform lower bound is needed.

## 5. The exact quadratic energy identities

Both e_p,0-u_p,0 and c+w^T e_0-1 have zero ambient differential at zero.
The latter assertion uses w^T Gamma=1^T. Their quadratic coefficients are
therefore unchanged if hazards are replaced by unconditional finite-date
clock atoms: the coordinate change has identity derivative at zero. This
makes the pairwise expansion transparent without dropping hazard corrections.

Let D_i denote the quadratic coefficient of e_i,0-u_i,0. For any tangent
satisfying (6), the coefficient for the pivot is

    D=D_p=sum_k a_pk g_k.                                       (8)

Observer contacts give D_i=0 for i!=p. This also follows from the explicit
pair formula below. For any symmetric P, summation by parts gives

    sum_k a_k^T P f_k=(1/2)sum_k a_k^T P a_k,

because f_0=f_N=0. Multiplying (6) by a_k^T P Gamma^-1 and summing proves

    D=-sum_k a_k^T QD a_k,                                     (9)

using PD v=e_p.

Write V for the quadratic coefficient of c+w^T e_0-1. For distinct i,j
put T_ij=sum_(k<l) a_ik a_jl and E_ij=sum_k a_ik a_jk. The fixed total
masses give T_ij+T_ji+E_ij=0. The pivot/observer debts have coefficients

    D_i=sum_(j!=i)[Gamma_ij T_ij-(J_ij-Gamma_ij)E_ij].            (10)

A passive pair among opponents does not affect (10): its contribution to
Never and the prescribed payoff is identical to quadratic order. The
weighted Never and joint-survival terms give

    V=sum_(i<j)[(w_i Gamma_ij-w_j Gamma_ji)T_ij
       +(w_i Gamma_ij-1+sum_(k notin{i,j})w_k T_k,ij)E_ij].       (11)

To verify (11), if i quits strictly before j, the loss from their two
singletons is weighted by the surviving outsider rows; summing those rows
uses sum_k w_k Gamma_ki=1. If the two dates coincide, the passive pair reward
adds precisely the last displayed weighted sum. These exhaust quadratic
events. Subtracting sum_i w_i D_i from (11) yields sum_k a_k^T K a_k with
K exactly as in (1). Since all observer D_i vanish,

    V=w_p D+sum_k a_k^T K a_k
     =-sum_k a_k^T QV a_k,                                    (12)

where the second equality repeats the summation-by-parts argument with
PV v=w_p e_p. Thus for every nonzero tangent in (6),

    D+rV=-sum_k a_k^T(QD+r QV)a_k<0.                          (13)

This is a coercive identity for arbitrary finite N; it does not rely on
a numerical eigenvalue calculation, a particular mode, or consecutive
strict dates. The finite rank test is a separate requirement.

## 6. From zero-data curvature to a genuine improvement

At zero data, the ambient differential of F in (5) is

    -Gamma_p sum_k dq_k-r sum_(k,i)dq_ik.

Adding the constraint combination e_p,0+r w^T e_0 makes that differential
zero. The contact multipliers, including fixed pivot-gap multipliers, are
all zero. Row independence in Section 4 makes these the unique stationary
multipliers. The resulting Lagrangian, up to a constant, is

    e_p,0-u_p,0+r[c+w^T e_0-1].                               (14)

Its constrained Hessian is strictly negative on every nonzero tangent by
(13), or by the alternative frequency calculation in Section 8A. On the
finite-dimensional unit tangent sphere it is uniformly negative.

If constrained local minima approached zero data, their multiplier equations
and the fixed invertible minor would force their multipliers to converge to
the unique zero-data multipliers. Their tangent spaces converge as well.
All derivatives through order two are continuous. Consequently the Hessian
of their Lagrangian would be negative on a nonzero tangent, contradicting
the second-order necessary condition for a local minimum on a smooth open
fiber. This proves the epsilon-neighborhood claimed in Section 2. Equivalently,
the exact fiber has either a nonzero first derivative of F, giving a descent
direction, or zero first derivative and negative second derivative.

In a positive-Never actual profile, each player's remaining conditional
finite mass tends to zero. Hence every late hazard tends to zero, all
conditional prescribed and Never payoffs tend to zero by the bounded-reward
union bound, and the conditional joint Never mass tends to one. Every
sufficiently late qualifying fixed window therefore lies in this neighborhood.
The exact splice in Section 3 proves the stated global-minimum exclusion.

## 7. Exact M14 certificate

Take four players, p=2, and

    Gamma=[0,-1,-1,2; -1,0,1,1; 1,2,0,-1; 1,-1,1,0],
    J=[0,-5,13,-5; 13,0,-5,-5; -5,-5,0,13; -5,13,-5,0].

All passive pair rewards are zero. Every reward on a coalition of size at
least three may be any fixed finite number for this controlled-window
obstruction. The canonical benchmark chooses -5 for participants and zero
for passive recipients. Here

    v=(4,5,1,3)/11,   w=(7,10,13,8)/11,
    PD=(1/10)[-4,2,12,-2; 2,-8,8,8; 12,8,-35,19; -2,8,19,-17],
    PV=(1/100)[-183,60,141,97; 60,-49,137,-44;
                          141,137,-282,111; 97,-44,111,-93].

Direct multiplication gives PD v=e2 and PV v=(13/11)e2. The leading
principal minors of QD and QV are, respectively,

    QD: 7, 3951/100, 290527/2000, 15333879/40000;
    QV: 4397/200, 1143956171/4840000,
         4506212701697/5324000000,
         905937923038697/1064800000000.

All are strictly positive, so Sylvester's criterion verifies (2). For the
same A,b as in Section 1,

    det A=12568/13611,
    det[b,Ab,A^2b,A^3b]=1043968/11440338672460347 != 0.

Thus four consecutive dates in S imply rank R_S=4, because the corresponding
four columns are an invertible power of A times this Krylov matrix, in
reverse order. If S also has a fifth date anywhere in the fixed window,
(3) holds. In particular five consecutive strict-pivot full-support dates
are impossible sufficiently late at an actual minimum. More generally,
intervening tied pivot dates are permitted by (3) and preserved exactly.

As a small independent regression for N=5,S={0,1,2,3,4}, order hazards by
date/player, and constraints by date/observer(0,1,3) followed by entrance
rows(0,1,2,3). Omitting variable q_3,4 gives determinant 77996937216.
A tangent is the five-row array

    ( 1045,   775,   970,  1747),
    (-4674, -3575, -4373, -7445),
    ( 7829,  6164,  7351, 11910),
    (-5820, -4708, -5464, -8476),
    ( 1620,  1344,  1516,  2264).

Its total mass is zero, and exact expansion gives
D=-1157984156, V=-5894461073/11, in agreement with (13).

## 8. Openness and exact remaining scope

For a fixed finite pattern (N,S), this is an open raw-matrix criterion.
Invertibility, the rank test and positive definiteness are open. The affine
constraints on PD,PV do not obstruct continuation under a small perturbation
of Gamma: v remains nonzero, and any symmetric P can be corrected smoothly
to solve P v=t for the desired target t. An explicit symmetric correction
for residual d=t-Pv is

    E=(d v^T+v d^T)/(v^T v)
                         -(d^T v)vv^T/(v^T v)^2,

which satisfies Ev=d. Apply this to targets e_p and w_p e_p. The strict
matrix inequalities then persist for all sufficiently small perturbations
of singleton, participant-pair and passive-pair rewards. Higher rewards
remain arbitrary fixed finite numbers; they affect the size of the small
window neighborhood, not the quadratic certificate.

The matrix criterion excludes controlled-window modes of actual minima in
this open family. The independent certificate below also covers an entire
unbounded premium ray. It does not say that every raw game in the family
has UE. In M14,
eventually full-support minima must keep meeting pivot-contact dates; fully
contact native Nash tails remain possible, as do sparse owner patterns and
inherited endpoints. The density consequence proved in Section 8B is
restricted to M14 and eventual full support; no variable-window uniformity,
source realization, or arbitrary Fin4 closure is asserted.


## 8A. A frequency certificate for the entire large-premium ray

This supplies the same strict finite-window curvature as the matrix energy
certificate for every real M>=14, with no upper bound on M. Use the same
singleton Gamma of Section 7, pivot2, and

    J(M)=[0,-5,M-1,-5; M-1,0,-5,-5;
                         -5,-5,0,M-1; -5,M-1,-5,0].

All passive pair rewards are zero. All rewards on coalitions of size at least three
are arbitrary fixed finite real numbers. The proof of Section 2
uses the raw matrix certificate (2) only to obtain strict negativity on the
zero-data tangent; the following direct identity supplies that conclusion
instead. The actual behavioral splice and fixed-pattern IFT argument are
unchanged. This is a mode exclusion, not an equilibrium-existence class.

### Fourier reduction with exact signs

Let a_k,f_k,g_k be any nonzero finite tangent satisfying

    f_0=f_N=0, Gamma f_k-J a_k=g_k e2, a_k=f_k-f_(k+1).

Extend these vectors by zero to integer dates. With Fourier convention
hat f(theta)=sum_k f_k exp(-ik theta), put w=1-exp(i theta). Then

    hat a=w hat f,
    (Gamma-wJ)hat f=e2 hat g.

Whenever the pencil is invertible, define T=w(Gamma-wJ)^-1 e2. Thus
hat a=T hat g. Parseval gives the quadratic coefficients from the general
pair expansion as

    D=(1/(2pi)) integral Re(T2)|hat g|^2,
    V=(1/(2pi)) integral [wbar2 Re(T2)+T* K T]|hat g|^2,       (15)

where wbar=(7,10,13,8)/11 is the real payoff weight, T* is conjugate
transpose, and K_ij=(wbar_i J_ij+wbar_j J_ji-1)/2 off the diagonal and
zero on it. In particular the notation wbar is not complex conjugation
of the scalar frequency w.

For a real t=tan(theta/2), set

    xi=2t^2-2it, B=(1+t^2)Gamma-xi J,
    Delta=det B, n=xi adj(B)e2.

The tangent-half-angle identity gives exactly T=n/Delta. Direct polynomial
identities give

    Re(n2 conjugate(Delta))=-2t^2(1+t^2)^4 F_D(M,t^2),
    (13/11)Re(n2 conjugate(Delta))+n* K n
                         =-(2/11)t^2(1+t^2)^4 F_V(M,t^2).    (16)

Here F_D=sum_(j=0)^3 d_j(M)y^j and F_V=sum_(j=0)^3 v_j(M)y^j, with

    d0=82M-423,
    d1=208M^3-1224M^2-5646M+36039,
    d2=128M^5-560M^4-6576M^3-66544M^2-337330M+3272259,
    d3=768M^6-2304M^5-21936M^4-487680M^3
                              -453096M^2-11316306M-95787;

    v0=292M+3183,
    v1=1216M^3-18000M^2+170772M+559637,
    v2=1152M^5-28032M^4+123520M^3+505680M^2
                                       +5247052M+24384253,
    v3=10368M^5+88832M^4+738368M^3+1987104M^2
                                       -34836004M-149601193.

Every coefficient of every polynomial d_j(14+u),v_j(14+u) is strictly
positive. This is a finite integer check by the binomial theorem on the
displayed eight polynomials. Consequently both F_D(M,y),F_V(M,y) are
strictly positive for M>=14,y>=0. Identity (16) then also proves Delta is
nonzero for real t!=0: if Delta vanished, its first real numerator would
be zero, a contradiction. At t=0, Delta=det Gamma=11. At theta=pi the
coefficient of t^16 in the first identity is -2d3(M)<0, which similarly
forces det(Gamma-2J) nonzero. Thus the pencil is invertible on the entire
unit-frequency circle, including the omitted tangent-half-angle point.

It follows that both real integrands in (15), apart from |hat g|^2, are
strictly negative except at theta=0. If g were identically zero, the
recurrence f_(k+1)=(I-J^-1 Gamma)f_k with f_0=0 would force a=0. Thus a
nonzero tangent has a nonzero trigonometric polynomial hat g. It cannot
vanish on an interval, and (15) implies D<0,V<0. In particular D+rV<0
for every r>=0 and every nonzero finite tangent. On each fixed finite
unit tangent sphere this is uniformly strict, exactly as needed by the
nonlinear local-minimum argument. No window-length-independent IFT
neighborhood is inferred.

### Uniformly available finite pattern

For every M>=14 the matrices J,A=I-J^-1 Gamma and the controllability
matrix are nonsingular. Their determinants are

    det J=-(M-11)(M-1)(M^2+8M+41),
    det A=(M^4-60M^2-942M-900)/[(M-11)(M-1)(M^2+8M+41)],
    det[b,Ab,A^2b,A^3b]
      =(M-6)^3(M^3+77M^2-982M+2029)
             /[(M-11)^4(M-1)^4(M^2+8M+41)^4],
    b=J^-1 e2.

The two nonobvious numerator polynomials have strictly positive
coefficients after M=14+u: they are

    u^4+56u^3+1116u^2+8354u+12568,
    u^3+119u^2+1762u+6117.

Hence any fixed window with at least five marked strict-pivot dates,
four of which are consecutive, passes the rank test. The finite-window
exclusion and its small-tail actual-source consequence therefore hold
throughout this entire unbounded premium ray. The threshold may depend
on M, the fixed window, the remaining finite reward entries and r.
This conclusion includes the canonical M14 table but does not assume
that its raw matrices PD,PV work unchanged for other M.


### Geometric remaining-mass decay throughout the premium ray

An actual minimum in this family with eventual full support also has a
geometrically decaying tail. Let f_i(k) be the conditional probability that
player i ever quits at or after physical date k, and beta_k=sum_i f_i(k).
Positive Never masses imply beta_k tends to zero. Every sufficiently late
five-date block contains a pivot-contact date by Section 2; full support
and observer optimality make that a contact date for all four players.

At any such full-contact date, the exact finite-event expansion gives

    e(k)=Gamma f(k)+O(beta_k^2),
    Q(q_k)=J q_k+O(beta_k^2),
    Gamma f(k)-J q_k=O(beta_k^2).

The first bound separates the event of only one opponent's finite clock
from the event of two or more finite clocks, whose probability is at most
beta_k^2/2. The second follows from the multilinear Quit formula and
q_ik<=f_i(k). The constants depend only on the fixed finite reward table.
Put L0=max(1,||Gamma^-1 J||_1). For all sufficiently late contact dates,
nonnegativity of f and q yields sum_i q_ik>=beta_k/(2L0).
The exact identity

    f_i(k)=q_ik+(1-q_ik)f_i(k+1)

gives beta_k-beta_(k+1)>= (1-beta_k)sum_i q_ik. Hence, after increasing
the cutoff so beta_k<=1/2, a full-contact date satisfies

    beta_(k+1)<=(1-eta)beta_k,    eta=1/(4L0)>0.

The sequence beta is nonincreasing at all other dates. The contact in
every late five-date block therefore proves

    beta_(k+5)<=(1-eta)beta_k,
    sum_(j>=k) beta_j <= (5/eta) beta_k.                         (17)

These estimates hold for every real M>=14 and all the fixed finite higher
rewards allowed above. They impose a further necessary condition on the
surviving eventual full-support actual source; they do not assert descent
on arbitrary growing windows or solve the sparse-support alternative.

## 8B. Zero-density consequence for the M14 full-support actual arm

For the displayed M14 matrices and zero passive pair rewards, any actual ALL-END observer minimum with positive Never masses and
EVENTUAL FULL SUPPORT has the following stronger necessary property:

    the set E of dates at which pivot2 strictly prefers Never
    has zero upper Banach density.

Here upper Banach density means
limsup_(L->infinity) sup_(a>=0) |E intersect{a,...,a+L-1}|/L.
The proof uses a fixed additive cube selected before applying the small-window
threshold. No theorem about long arithmetic progressions is needed.

### All powers are controllable

The characteristic numerator of A=I-J^-1 Gamma is

    f(x)=13611x^4-54692x^3+81334x^2-52832x+12568.

It is irreducible over Q. Modulo7 its monic normalization is
h=x^4+2x^3-2x^2-x+1, and

    R=(x^49-x) mod h=-2x^3-x^2+x+1,
    (-2x^2+2x-2)R+(3x+3)h=1 mod7.

Thus h has no irreducible factor of degree1 or2. A reducible quartic has
such a factor, proving irreducibility over F7 and then over Q.

A has a unique eigenvalue of smallest complex modulus. To see this without
a numerical spectrum, put

    p(z)=f(1-z)=13611z^4+248z^3-1076z^2-204z-11.

There is exactly one positive root rho by Descartes' sign rule, and
p(1/3)=-64/3<0<p(7/20)=107691/160000, so 1/3<rho<7/20. Factor

    p(z)=(z-rho)(13611z^3+Bz^2+Cz+F),
    B=248+13611rho>4785,
    C=-1076+rho B>519,
    F=11/rho<33.

All cubic coefficients are positive and BC>4785*519>13611*33>13611F.
Every cubic root has negative real part. Indeed a nonnegative real root
is excluded by coefficient signs; if a conjugate pair x+-iy had x>=0,
the remaining real root would be -b<0, and the normalized coefficients
would satisfy c2*c1-c0=-2x[(b-x)^2+y^2]<=0, contrary to BC>13611F.
Thus the other three A eigenvalues have real part greater than one,
whereas lambda=1-rho lies in(13/20,2/3). This proves the unique-smallest-
modulus claim. All roots are nonzero and distinct by irreducibility in
characteristic zero.

No ratio of two distinct A eigenvalues is a root of unity. If alpha/beta
were such a root, a Galois automorphism of the splitting field could send
alpha to the unique smallest-modulus root lambda, by irreducibility.
It sends beta to a different root beta', and sends alpha/beta to another
root of unity. But |lambda/beta'|<1, a contradiction.

The exact nonzero determinant det[b,Ab,A^2b,A^3b] proves b is cyclic for A.
In a complex eigenbasis, all four components of b are therefore nonzero.
For every nonzero integer d the eigenvalues of A^d are still distinct,
since no ratio is a root of unity. The Vandermonde determinant then proves
b is cyclic for A^d as well.

### Every three-dimensional additive cube passes the rank test

Choose positive integers d1,d2,d3 with d2>d1 and d3>d1+d2. Let

    S={eps1*d1+eps2*d2+eps3*d3: epsj in{0,1}},
    N=1+d1+d2+d3.

The eight dates are distinct. The matrix R_S has rank4. Multiplying all
its columns by A^(-(N-1)) reduces them to A^(-s)b, s in S. Starting with
V0=span{b}, define Vj=V(j-1)+A^(-dj)V(j-1). If dimV(j-1)<4 and this
operation did not increase dimension, V(j-1) would be an A^(-dj)-invariant
proper subspace containing b, contrary to cyclicity. After three steps
the dimension is at least4, hence exactly4. Thus S satisfies the finite
controlled-window criterion, including |S|>=5.

### An elementary positive-density cube lemma

If F subset N has positive upper Banach density, then for every integer
H>=1 there exists d>=H such that F intersect(F-d) also has positive upper
Banach density. Here F-d={n:n+d in F}.

Choose delta>0 and arbitrarily long intervals I of length L with
|F intersect I|>=delta L. Fix M>=8/delta^2. For L sufficiently large,
every shifted set F-jH, 0<=j<M, has at least delta L/2 points in I.
Let m(t) count how many of those M sets contain t. Cauchy--Schwarz gives

    sum_(i<j) |(F-iH) intersect(F-jH) intersect I|
      =(sum_(t in I) m(t)^2-sum_(t in I)m(t))/2
      >=(M^2 delta^2/4-M)L/2
      >=M^2 delta^2 L/16.

Some pair therefore has intersection size at least delta^2 L/8. There
are only finitely many pairs; one pair recurs along intervals with lengths
tending to infinity. Translating its intersections by iH proves that
F intersect(F-(j-i)H) has positive upper Banach density, with d=(j-i)H>=H.

Apply this lemma to E, then to E intersect(E-d1), then to the latter
intersection and its shift. Choose each new H larger than the sum of
previous steps. The result is fixed superincreasing d1,d2,d3 and a set

    F3=intersection_(s in S)(E-s)

of positive upper Banach density. In particular F3 has arbitrarily large
elements. Each a in F3 supplies all eight strict pivot dates a+S.

If E had positive upper Banach density, this construction would give one
fixed N,S passing the rank test and arbitrarily late translates of that
pattern. Eventual full support supplies positive hazards at every physical
date between its endpoints. The fixed-pattern theorem gives one late cutoff
for this N,S, after which no such translated strict pattern is possible.
This contradicts the unbounded set F3. Hence E has zero upper Banach density.

The remaining full-support mode may have pivot contacts at all dates or
strict comparisons on a zero-density set. Sparse owner supports and non-
actual inherited endpoints remain outside this corollary. The cube proof
requires no quantitative uniformity in N or in the chosen steps.

## 9. Source correspondence and implementation boundary

The complete stopping-law payoff is
`quittingStoppingLawExpectedPayoff`, and its unrestricted replacement-law
cap is `quittingStoppingLawReplacementPayoffCap`, in
[StoppingLawOperationalDistance.lean](../../UniformEquilibrium/Quitting/Paths/StoppingLawOperationalDistance.lean).
The declarations
`quittingStoppingLawExpectedPayoff_behaviorStoppingLaws_eq_terminalPayoff`
and
`quittingStoppingLawCap_behaviorStoppingLaws_eq_continuationBestResponseValue`
identify these objects with the prescribed payoff and full behavioral cap
of an arbitrary behavior profile. Conversely,
`quittingTerminalPayoff_stoppingLawProfile_eq_expectedPayoff` and
`quittingStoppingLawCap_eq_continuationBestResponseValue_stoppingLawProfile`
give those identities for the canonical independent conditional-hazard
implementation of supplied laws. These are the precise operational bridges
used in the actual-data adapter; the observer cap is never replaced by a
stationary-response cap. The same file's
`pmfOperationalDistance_finitePrefixStoppingLaw_le` verifies continuity of
the finite hazard modification with its unchanged tail.

In [TerminalSemanticPair.lean](../../UniformEquilibrium/Quitting/Root/TerminalSemanticPair.lean),
`quittingTerminalSemanticPair` is exactly (U,B), and
`quittingTerminalSemanticDebt` is B-U. The declaration
`quittingTerminalSemanticPair_rootThenContinuation` equates the semantic
prefix map with a literal independent root followed by its continuation.
Iterating this identity gives the finite polynomial recursions (4), and
its max-Quit/Continue cap recursion matches the behavioral induction in
Section 3. The new mathematics is the fixed-entrance-cap constraint fiber,
its coercive second variation, and the resulting actual-minimum exclusion;
none is assumed as a field of a semantic pair.

The established global theorem
`not_exists_uniformEquilibriumPayoff_iff_hasPositiveMinimumTerminalSemanticDebt`
in [PositiveMinimumSemanticDebt.lean](../../UniformEquilibrium/Quitting/Terminal/PositiveMinimumSemanticDebt.lean)
concerns minimum total debt on the compact semantic carrier. The theorem
`exists_positive_minimumTerminalSemanticDebt_face_of_no_uniformPayoff`
in [TerminalSemanticEqualityStratum.lean](../../UniformEquilibrium/Quitting/Root/TerminalSemanticEqualityStratum.lean)
provides a positive-debt face and its exact-root restrictions. Neither
statement asserts that the carrier minimum is actual, that it minimizes
J_r=d_p+r nu on the observer carrier, or that a given tail has the window
pattern (3). This packet does not silently infer any of those conclusions.
Its adapter applies once the actual observer-minimum arm is selected, and
strictly removes the specified configurations within that arm.

The implemented `quittingSingletonPacketQuadraticEnergy` and
`quittingSingletonPacketQuadraticEnergy_eq_symmetricEnergy` in
[SingletonPacketEnergy.lean](../../UniformEquilibrium/Quitting/Classification/SingletonPacketEnergy.lean)
concern one real singleton mass vector and a symmetric one-packet
energy. Their inputs have neither the signed multi-date tangent equations
(6), the fixed-cap endpoint constraints, nor the participant/passive-pair
correction (1). They do not yield (13) or its full-cap-preserving descent.
The present certificate is a strict additional mode exclusion, not a new
name for that implemented quadratic form. All source declarations named
here refer to tracked Lean source; this packet itself claims ordinary
mathematical proof, not an already checked Lean implementation.

## 10. Boundary tests and attempted falsifiers

The exact M14 data and positive principal minors in Section 7 supply a
positive test of every raw premise and a nonzero admissible tangent. The
five-date determinant and quadratic coefficients are independent finite
regressions for the same conclusion. Section 8A adds exact all-frequency
polynomial identities and a complete M>=14 positivity test. Section 8B
checks irreducibility and the unique-smallest-modulus spectrum before using
all-power controllability; mere simplicity of A would not suffice because
roots-of-unity eigenvalue ratios could destroy the spaced ranks.

If every pivot date is tied, take S empty. Then |S|>=n+1 fails; with full
contacts and fixed entrance values, (7) has g=0 and f_0=0, hence f=0 and
there is no tangent. Fully contact native Nash tails are therefore not
contradicted. More generally |S|<=n gives no positive-dimensional kernel
when the endpoint rank is n; a rank-deficient case is not repaired by
counting variables. For fewer than n controls, full endpoint rank is
impossible. The theorem explicitly requires both rank and dimension.

A missing owner hazard places the original point on a face of the cube.
The two-sided open IFT fiber need not lie in that face, so sparse support
patterns are outside the result. Likewise a marked pivot contact cannot
be treated as a strict inequality: it must be placed outside S and fixed
exactly, possibly reducing the dimension below the required threshold.
Empty dates cannot be removed without checking their native Quit0 options;
this proof uses consecutive physical dates throughout.

Arbitrarily long windows are not a free source of uniformity. Although the
energy identity is valid for all N, the IFT inverse and the resulting
epsilon may depend on the fixed pattern (N,S). A sequence of growing
windows with vanishing hazards does not by itself meet the theorem's
quantifiers. The theorem also does not preserve an arbitrary imposed
pivot prescribed payoff: that payoff is precisely what can improve while
all full caps are preserved.

For passive pair perturbations the K correction in (1) is essential.
For example, changing one outsider reward T_i,jk by delta changes V by
w_i delta E_jk. Omitting this term would give a false quadratic identity
even with Gamma,J unchanged. Participant triples and higher coalitions
do not give such a term: their direct events have degree at least three,
and their contact-constraint Hessians have zero zero-data multipliers.
The strict positive-definiteness tests must be rerun after a large change
of any reward entering (1); no arbitrary-pair-reward claim is made.

## 11. Actual-source adapter and residual consumer

Define the actual observer-minimum configurations to be actual independent
profiles with positive marginal Never masses, ALL-END, zero debts outside
p, and global minimality of J_r on a carrier containing every actual
observer-optimal profile. This definition imposes no unproduced rate or
return witness. Starting with any such configuration, extract its literal
hazards and its conditional whole tail after the proposed fixed window.
All observer contacts follow from zero observer debt and positive hazards;
ALL-END gives the pivot comparisons. Bounded rewards and positive Never
masses give the small-tail limits proved in Section 6. Thus every hypothesis
of the window theorem is supplied by the actual incoming configuration
and the explicit finite pattern being tested.

For the four-player raw example, let I4 denote the actual branch in which
all four owners have infinitely many positive finite clock atoms. Partition
this branch further by its literal late hazard supports and pivot contacts.
The subclass with eventually full support and eventually strict pivot-Never
comparisons is impossible: every sufficiently late five-date physical
window has S={0,1,2,3,4}, satisfies (3), and contradicts Section 2. More
generally every fixed finite pattern passing (3) is excluded if it recurs
arbitrarily late with all its marked comparisons strict. Throughout the
premium ray, the eventual full-support source has geometric remaining-mass
decay. At M14 the elementary cube argument further forces the strict-date
set to have zero upper Banach density whenever full support is eventual. The conclusion is
an explicit necessary restriction on the surviving actual I4 source, not a
conditional strategy-existence interface.

The finite-support arm, sparse I4 calendars, eventual all-contact tails,
and non-actual inherited endpoints remain separate. The raw energy test
is not asserted for every singleton matrix. No strategy-class completeness,
original-game uniform-equilibrium payoff, or full Fin4 closure is claimed.

## 12. Lean handoff

A narrow formalization can define a raw matrix certificate carrying only
Gamma,J,w,v, the symmetric matrices PD,PV, their linear identities and the
positive-definiteness proofs, with the explicit premium family as a separate
raw alternative proved by the displayed frequency polynomials. A separate finite predicate on N,S records
rank R_S=n and |S|>=n+1. Neither structure should contain an improving
profile, an excluded minimum, or a desired equilibrium conclusion.

First prove the finite polynomial contact derivative, the state/control
rank equivalence, and the quadratic identities (9)--(13). Then establish
an analytic finite-window lemma: for every certificate, r and fixed rank
pattern, there exists epsilon>0 such that every strictly feasible window
with sufficiently small continuation data has an exact feasible window
with the same entrance caps and smaller objective (5). The IFT and the
second-order necessary condition supply this witness; it is not an input.
The exact rational M14 data should be a closed example of the matrix and
rank predicates, with the displayed principal minors as finite arithmetic
checks. The premium-ray alternative additionally needs only finite Fourier
Parseval for finitely supported sequences and the exact polynomial sign
identities. The geometric-tail consumer uses only the one-clock/two-clock
probability split and the exact remaining-mass recursion. The density
corollary needs irreducible-polynomial Galois transitivity, finite-dimensional cyclicity and the elementary finite
translate-intersection count; it does not import a long-progression theorem.

Finally combine the window lemma with literal finite root splicing and
the operational stopping-law/behavior bridges. A suitable theorem shape is:
for every raw certificate and fixed rank pattern, every actual ALL-END
observer minimum with positive Never masses has a cutoff beyond which no
qualifying strict marked full-support window occurs. Specializing to the
M14 five-date pattern gives the explicit actual I4-mode exclusion. The
augmented closure's realization question is intentionally a different
formal obligation.
