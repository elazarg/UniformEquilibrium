# Positive continuation caps for a cyclic joining-increment chamber

This ordinary mathematical result partitions positive continuation caps by
explicit polynomial inequalities for an arbitrary raw table in the chamber
below. It gives a necessary condition at every positive subcritical global
minimum. The M14 benchmark supplies an exact boundary control; its UE is
proved separately by the [direct return producer](../exports/NO_CHILD_PREMIUM_FAMILY_UNIFORM_EQUILIBRIUM.md).
This cap-region theorem does not assert that a particular cap vector is an
executable continuation or produce UE for every table in the chamber.

## Raw hypotheses and exact root map

There are n>=3 players. The native reward Z_i(S) is finite for every
nonempty coalition S. Each own singleton and Never reward is zero. A root
consists of n independent Continue/Quit choices followed by continuation
v if everybody Continues. For every nonempty opponent coalition D define
its joining increment

    Delta_i(D)=Z_i(D union {i})-Z_i(D).

Put L_ii=0 and L_ij=Delta_i({j}) for i!=j. Assume:

- Each row i of L has exactly one positive entry, at pred(i); all other
  off-diagonal entries are strictly negative. The predecessor permutation
  is one cycle containing all n players.
- L is invertible and A=L^-1 is strictly positive entrywise.
- Delta_i(D)<0 whenever D has at least two players.

These are finite raw reward tests. Passive rewards themselves may have
either sign; only their stated joining differences are constrained. Write

    R_i(x)=sum_(D subset I minus {i}; |D|>=2)
                         [-Delta_i(D)] prod_(j in D) x_j,
    C(x)=Lx-R(x).                                    (1)

Every R_i has binom(n-1,2) strictly positive quadratic coefficients, and
strictly positive coefficients at all its higher monomials. For a root without sure quitters let
`x_j=q_j/(1-q_j)`. If Q_i and P_i denote its Quit and passive Continue
offers and H_i the opponent survival, the exact indifference equation is

    (Q_i-P_i)/H_i=sum_(nonempty D subset I minus {i})
                              Delta_i(D) prod_(j in D)x_j
                 =C_i(x)=v_i.                       (2)

Own singleton zero removes the empty-coalition term.

## Complete support reduction

There is no Nash root containing a sure quitter, for any continuation v.
If j surely quits, every k other than j and its positive-increment successor
strictly Continues: every opponent coalition containing j has negative
joining increment for k. The successor then strictly prefers Quit, since
its only opponent quitter is j and their linear increment is positive.
Player j now strictly prefers Continue, since n>=3 makes its reverse
singleton increment negative. This contradicts its sure Quit. No continuation
payoff enters any of these comparisons.

Suppose v>0 coordinatewise. In any nonzero root without a sure quitter,
let S be the players with positive quitting probability. If S is proper,
some i in S has pred(i) outside S. Every remaining active linear
coefficient in C_i is strictly negative,
and R_i>=0. Thus the right side is nonpositive, contrary to v_i>0.
Consequently every nonzero Nash root at positive v is fully mixed.

Conversely every solution of(2) gives a fully mixed Nash root by
`q_i=x_i/(1+x_i)`. AllContinue is always a strict Nash root when v>0.

## The explicit region D

Define

    D={v>0: exists x>0, C(x)=v}.

Root existence is equivalent to either of the finite tests

    exists x>=0, F_v(x)<=x,
    F_v(x)=A[v+R(x)],                                (3)

or, equivalently, `exists x>0, C(x)>=v`.
The nontrivial direction follows by monotone iteration from x0=0:
`x_(n+1)=F_v(x_n)`. A supersolution bounds this increasing sequence;
its limit is a fixed point, and strict positivity of A and v makes the
limit strictly positive. The limit x_min(v) is no larger than any other
fixed point.

D is downward closed within the positive orthant. It is also logarithmically
convex: if x,y are supersolutions for v,w, respectively, put
`z_i=x_i^theta y_i^(1-theta)` and
`u_i=v_i^theta w_i^(1-theta)`, for 0<=theta<=1.
Each `F_v(x)_i/x_i` is a finite sum of positive monomials in x and v.
Termwise weighted Holder gives

    F_u(z)_i/z_i <= [F_v(x)_i/x_i]^theta
                         [F_w(y)_i/y_i]^(1-theta)<=1.

Thus u belongs to D. Formula(3) is consequently a finite convex feasibility
problem after taking logarithms of its positive variables and dividing
each inequality by x_i; no infinite strategy search is involved.

D contains a positive box. Put h=A1>0, K=max_i R_i(h)>0, and
`s0=min(1,1/(2K))`. Because R has no monomials of degree below two,
`R_i(s0 h)<=s0^2 K`. Consequently we have
`C(s0 h)>=s0/2`. Hence every positive v with coordinates at most s0/2
belongs to D. This does not assume that L has positive row sums.

Every fixed point has an a priori uniform bound. Put
`a=min A_ij>0`, `b=max A_ij`, `kappa=a/b`, and let c>0 be the minimum
of all quadratic coefficients of R. Since `x=A[v+R(x)]`,
`min x_i>=kappa max x_i`. Writing X=max x_i gives, for every row,

    R_j(x)>=binom(n-1,2)c kappa^2 X^2,
    x_i>=a sum_j R_j(x)>=n binom(n-1,2)a c kappa^2 X^2.

Consequently `X<=1/[n binom(n-1,2)a c kappa^2]`.
Also x_i>=a sum_j v_j, so D is
bounded. If positive v_n in D
converges to positive v, a subsequence of its bounded roots converges to
a root of v. Its coordinates stay positive because x_n>=A v_n.
Thus D is relatively closed in the positive orthant.

## Minimal roots, exact Perron boundary and radial partition

At the minimal root set `T=DF_v(x_min)=A DR(x_min)`. This matrix is
strictly positive, since x_min>0. Its Perron eigenvalue satisfies rho(T)<=1.
Indeed if rho>1 and k>0 is its Perron vector, then for sufficiently small
eta>0 the vector `x_min-eta k` remains positive and is a strict
supersolution by Taylor expansion. Monotone iteration below it gives a
smaller fixed point, contradicting minimality.

If rho(T)<1, the inverse of I-T is its positive Neumann series; IFT
continues the root for every sufficiently small perturbation of v.
Thus v is an interior point of D.

If rho(T)=1, no strictly larger positive target v+b, b>0, can have a root.
For any such root y, monotone iteration at v gives y>=x_min. Put
d=y-x_min>=0. Every component of R is convex along nonnegative directions,
so

    d=F_(v+b)(y)-F_v(x_min)>=T d+A b.

Multiplying by a strictly positive left Perron vector of T contradicts
its eigenvalue one. Hence v lies on the boundary of D. These arguments
prove the exact criterion

    v in boundary D iff rho(A DR(x_min(v)))=1.         (4)

The critical root is unique. Any other fixed point y dominates x_min,
and if unequal its difference d is strictly positive because A>0 and
DR>0 off the diagonal at positive arguments. Strict convexity along d
would give `d=F_v(y)-F_v(x_min)>T d`, contradicting the positive left
Perron vector. Thus a boundary cap has exactly one nonzero Nash root.

Conversely, any positive root x with rho(A DR(x))<=1 is the minimal root.
Otherwise its strictly positive difference d from the minimal root would
satisfy `A DR(x)d>d` by strict Taylor expansion, forcing its Perron
eigenvalue above one. Thus the boundary has the direct finite description

    {C(x): x>0, C(x)>0, rho(A DR(x))=1}.

At such a point the critical eigenvalue is simple, with positive left and
right vectors. The root map has a nondegenerate fold: a right kernel k of
DC is positive, a left kernel is `l^T A>0`, and

    (l^T A) D^2 C(x_min)[k,k]
                       =-(l^T A)D^2R(x_min)[k,k]<0.

The last inequality is strict because all k_i>0 and each R_i contains
at least one positive pair monomial. Resolving the n-1 transverse variables
by IFT reduces to one scalar equation with nonzero second derivative
and nonzero derivative in any positive target direction. This is the
usual elementary fold normal form, rather than an assumed branch extension.

Every positive target ray `{tau v0:tau>0}` therefore meets D in exactly
an interval `(0,tau*]`, with finite positive tau*, and its endpoint obeys
(4). Before the endpoint the minimal root is regular; at the endpoint it
is critical; beyond it AllContinue is the unique Nash root. This is a
complete positive-cap root partition for every raw table satisfying the
stated joining-increment hypotheses.

## An exact positive fold and a useful excluded minimum-cap box

Specialize to the M14 benchmark:

    Gamma=[0,-1,-1,2; -1,0,1,1; 1,2,0,-1; 1,-1,1,0],
    J=[0,-5,13,-5; 13,0,-5,-5; -5,-5,0,13; -5,13,-5,0].

Every larger participant reward is -5 and every passive nonsingleton
reward is zero. Thus all higher joining increments are -5, while

    L=J-Gamma=[0,-4,14,-7; 14,0,-6,-6; -6,-7,0,14; -6,14,-6,0],
    A=(1/6284)[714,1057,810,609; 732,714,672,994;
               994,609,758,663; 672,810,1132,758].

All general hypotheses hold, with positive-increment cycle
`0 -> 1 -> 3 -> 2 -> 0`. In this specialization
`R_i(x)=5[sum_(j<k; j,k!=i)x_j x_k+prod_(j!=i)x_j]`.
The explicit positive inner box may be taken to have side539/32768,
because all coordinates of `C((1/32)1)` are at least this number.

Let a* be the first positive root of

    p(a)=-3a^4+8a^3-688a^2+19508a-12568.

Direct substitution gives

    p(659/1000)=-9289598528883/10^12<0,
    p(33/50)=58237037/6250000>0.

Moreover p'>0 throughout[0,33/50], for example by
`p'>=19508-1376(33/50)-12(33/50)^3>0`. Thus a* lies strictly between
these rational bounds and no earlier positive root occurs. Put

    s*=sqrt(1+a*/5)-1, x*=s*1,
    v*=(3,2,1,2)s*-(15s*^2+5s*^3)1.                  (5)

We have `0<s*<8/125`, because `5[2(8/125)+(8/125)^2]=2064/3125>33/50`.
Every v*_i is positive: its smallest coordinate is
`s*[1-15s*-5s*^2]>s*(61/3125)>0`.

At uniform x=s1, `DC=L-aK`, where `a=5(2s+s^2)` and K=11^T-I.
Its determinant is p(a). The matrix AK is strictly positive. Its first
positive singular parameter is `a=1/rho(AK)`, which must be a* by the
preceding isolation. Therefore `DF_(v*)(x*)=a* AK` has Perron eigenvalue
one. Monotone iteration has minimal fixed point m<=x*. If m<x*,
the general nonminimal-root criterion would force its Perron eigenvalue
above one. Thus m=x*, and(4) puts v* on the boundary. The general
critical-root uniqueness proves x* is the unique nonnegative root there.
For every tau>1 there are no nonzero Nash roots at tau v*.

The same comparison gives two explicit cones, stronger than coordinatewise
comparison with v*. If `A(v-v*)<=0`, then x* is a supersolution for v and
v belongs to D. If `A(v-v*)>=0` and is nonzero, no root exists: any
putative root dominates the minimal root x*, and the positive left Perron
vector contradicts the nonnegative, nonzero extra forcing. These statements
are restricted to v>0; they do not change the continuation domain.

At this exact fold the fully mixed root's current native payoff is the
strictly positive uniform vector

    Q_i=[3s*-15s*^2-5s*^3]/(1+s*)^3.

The fold occurs with hazards strictly between zero and one, positive
continuation, and positive current cap. It is not a support or sure-quit
boundary. This does not assert that v* lies on the earlier executable
native-Nash stable curve.

Strict higher-increment negativity is substantive. Keep the displayed
linear matrix L, set every off-diagonal singleton reward to zero, every
participant-pair reward to L_ij, and all remaining rewards to zero. Then
all higher joining increments vanish and C(x)=Lx. Every positive target
has the positive solution x=A v; D is the entire positive orthant, with
no bounded radial threshold or Perron fold. Thus the negative higher
increments cannot simply be deleted from the compactness/fold theorem.

## Consumer at a positive subcritical minimum

Suppose a source selects a global minimum with payoff U, full cap B>0,
zero debts off a selected pivot p, pivot debt d_p, Never product nu, and
strictly positive objective `mu=d_p+r nu`, r>0. Its feasible semantic carrier is closed
under finite independent root prefixing; this holds for actual profiles
and for their augmented closure by continuity of the finite prefix map.

If B were in D, take its nonzero Nash root. Let c in(0,1) be this root's
joint Continue probability. Root indifference at B gives a current cap T.
Replacing continuation B by its actual prescribed U changes the current
prescribed row i by exactly `c(B_i-U_i)`. Thus the new full debt is
`d'_i=c d_i`, while `nu'=c nu`. The zero observer debts are retained and
the objective becomes `c mu<mu`, contradicting minimality.

Consequently every such global minimum for any table in the stated chamber
satisfies the explicit condition `B not in D`: its positive cap ray lies
strictly beyond the unique Perron boundary in(4). In the M14 specialization,
it cannot have `0<B<=v*` coordinatewise, nor can every coordinate be at
most539/32768. The stronger explicit finite M14 test is

    at least one coordinate of A B exceeds that of A v*.

Indeed the opposite four weak inequalities make x* a supersolution by
the preceding cone test. All coefficients of A and the algebraic number
s* are specified in this proof.

This is a necessary condition at the selected global minimum, not a claim
that outside D is an equilibrium obstruction or that all source points
are actual. It does not preserve an inherited head's fixed observer caps
and is not an admissible variation inside that separately constrained fibre.

## A whole reward-box consumer

The [finite vertex criterion](CODEX_COORDINATOR__FINITE_VERTEX_CAP_ROOT_CRITERION.md)
provides a complete equilibrium conclusion under an additional raw box test.
In this cyclic chamber, write H_i=max(0,max_D Z_i(D)). If an explicit
supersolution xbar>0 satisfies C(xbar)>=H, monotone iteration supplies a
nonzero root at every nonzero nonnegative attainable cap. The stronger
all-marginal-finite carrier minimum then gives approximate full Nash profiles
and UE after arbitrary signed row offsets. This condition is sufficient;
it is not asserted necessary or supplied by every table in the chamber.
The general vertex theorem permits signed higher joining terms and does not
require L inverse-positive. Its coverage beyond existing stationary and
other existence criteria remains unproved, so no additional Fin4 class is
counted from this consumer yet.
