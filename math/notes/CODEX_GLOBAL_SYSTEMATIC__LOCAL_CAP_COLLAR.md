# A local cap collar excludes an absorbing zero face

Owner: CODEX_GLOBAL_SYSTEMATIC. Proved ordinary mathematics, independently
[reviewed](../feedback/CODEX_GLOBAL_SYSTEMATIC__LOCAL_CAP_COLLAR__BY_CODEX_LOCAL_COLLAR_REVIEW.md)
and [adversarially checked](../feedback/CODEX_GLOBAL_SYSTEMATIC__LOCAL_CAP_COLLAR__BY_CODEX_COLLAR_ADVERSARY.md).
Not Lean checked. This excludes a boundary face for the unequal-premium
calibration, including its all-zero endpoint. It does not construct an
equilibrium or settle Fin4.

The strict increment over the existing
[weighted cap theorem](CODEX_COORDINATOR__WEIGHTED_CAP_ABSORPTION_COERCIVITY.md)
is that weighted forced-Quit rewards need only be positive near the zero root.
A separate raw root test prevents a small cap vector from jumping out of that
neighborhood. On the calibration below, EVERY weight satisfying positive
singleton drift fails the older global forced-Quit test.

## 1. Native semantics and the raw tests

There are n>=2 players. Each independently chooses a private law on the
natural dates and Never. The first nonempty quitting coalition A pays the
bounded vector Z(A); live and AllNever pay zero. Assume Z_i({i})=0 and
|Z_i(A)|<=M, with M>=1. A unilateral replacement may be any complete law,
including every deadline and Never. Let B_i be its full response supremum,
N_i its prescribed Never mass, and nu=product_i N_i. Let K_abs be the closure
of actual absorbing payoff/cap pairs, where absorbing means nu=0.

For a product root q in[0,1]^n put s=sum_i q_i. Write Q_i(q) for the
forced-Quit payoff, P_i(q) for the nonempty-opponent contribution when i
Continues, and H_i(q)=product_(j!=i)(1-q_j). Put Gamma_ij=Z_i({j}), including
Gamma_ii=0. These are polynomials determined by the raw reward table.

Fix a probability vector z supported on S, with every z_i>0 on S. Suppose:

1. sigma_j=sum_i z_i Gamma_ij>=gamma>0 for every j;
2. Z_i({i,j})>=m>0 for every i in S and j!=i;
3. the only q in[0,1]^n with Q_i(q)<=0 for every i in S is q=0.

The third condition is a statement about finitely many explicitly given
polynomials, not about an equilibrium, continuation or selected strategy.
One sufficient finite reward test for it is: some a in S has
Z_a(A)>0 on EVERY coalition containing a with |A|>=2. Indeed Q_a(q)>0
whenever any opponent of a has positive hazard. If all those hazards vanish,
any b in S different from a has Q_b(q)=Z_b({a,b})q_a, which is positive
unless q_a=0. Such b exists because condition 1 and Gamma_aa=0 forbid
support(z) from being a singleton.

**Theorem.** Under these raw tests there is a produced constant delta>0 such
that EVERY actual profile satisfies

    max_(i in S) B_i >= delta*(1-nu).                         (1)

Every actual absorbing profile has max_(i in S)B_i>delta, and every point
of K_abs has max_(i in S)B_i>=delta. Thus the entire face B_i=0 for i in S
is absent from K_abs, without restricting the other coordinates or debts.
Equation(1) also passes to the augmented closure retaining the original N_i.
Its only point with max_(i in S)B_i=0 is the AllNever tuple, with every
payoff and cap zero and every N_i=1.

All statements concern native Z with literal Never zero. No translation of
an original game's live or Never payoff is being made.

## 2. Explicit constants and the local estimates

Let z_* be the smallest positive weight, z^* the largest weight, and choose

    rho=min(1/4,m/(4M),gamma/(8M)),
    kappa=(m/2)*(1-z^*)>0.

For i in S let t_i=sum_(j!=i)q_j. On s<=rho, the singleton-opponent events
give at least m*t_i*(1-t_i), and the events with two or more opponents
have probability at most t_i^2/2. Therefore

    Q_i(q)>=m*t_i-(m+M/2)*t_i^2 >= (m/2)*t_i>=0,
    sum_i z_i Q_i(q)>=kappa*s.                              (2)

The same elementary expansion gives

    |P_i(q)-(Gamma q)_i|<=(3M/2)*s^2.

Indeed the probability loss from replacing singleton-event probabilities
by q_j is at most t_i^2, and the multi-opponent probability is at most
t_i^2/2. Consequently

    sum_i z_i P_i(q)>=gamma*s-(3M/2)*s^2>=gamma*s/2.          (3)

By condition 3, continuity and compactness, the number

    d_0=min_(q in[0,1]^n, sum q>=rho) max_(i in S)Q_i(q)

is strictly positive. Put eta=d_0/2. If an actual profile has
b=max_(i in S)B_i<=eta, its first root satisfies Q_i(q)<=B_i, so s<rho.
Equations(2) then imply B_i>=0 on S and, writing w=sum_i z_i B_i,

    0<=w<=b,       w>=kappa*s,       B_i<=w/z_*  (i in S).  (4)

Every actual profile has b>=0: condition 3 gives a strictly positive
forced-Quit coordinate at a nonzero first root; a zero first root instead
has every forced-Quit coordinate zero.

Define

    K=2/z_*+2M/kappa,
    delta=min(eta,eta/K,gamma/8).                            (5)

The constants are obtained entirely from the table and z. The minimization
defining d_0 is finite dimensional over a compact semialgebraic set. No
strategic object is an input.

## 3. The collar is invariant and limits total activity

For an actual profile with b<=delta, its first root has s<rho<=1/4, so all
conditional tail laws are defined. Let C be their full cap vector and
v=sum_i z_i C_i. The exact full-response recursion is

    B_i=max(Q_i(q),P_i(q)+H_i(q)C_i).                       (6)

Since H_i>=1-s>=1/2 and |P_i|<=M*s, equations(4) give, for i in S,

    C_i<=(B_i-P_i)/H_i<=2(B_i+M*s)<=K*w<=eta.             (7)

Apply the small-cap conclusion(4) AFRESH to the actual conditional tail.
It yields C_i>=0 on S and v>=0. We can therefore use (3) and H_i>=1-s
in the Continue branch of(6):

    w>=gamma*s/2+(1-s)v.

Because w<=delta<=gamma/8, this implies

    0<=v<=w-(gamma/4)*s<=w.                              (8)

The same argument repeats. The first tail has supported caps at most eta,
nonnegative supported caps, and weighted cap v<=w<=delta. At every later
step, these facts imply(2),(4),(7),(8), even if its maximum cap is larger
than delta. Thus no assumption that the maximum itself decreases is used.
Every finite survival is positive, and summation gives

    sum_t sum_i q_(t,i)<=4*w_0/gamma,
    1-nu<=sum_t sum_i q_(t,i)<=4*w_0/gamma<=4*b/gamma.    (9)

For b<=delta, (9) proves(1), since delta<=gamma/8<gamma/4. For b>delta,
(1) follows from 1-nu<=1. Equation(9) also proves nu>=1/2 when b<=delta,
so every actual absorbing profile has b>delta.

The inequalities pass to K_abs and to the augmented closure by continuity.
If b=0, (1) forces nu=1 and hence N_i=1 for every i. On every actual native
profile, |U_i|, |B_i| and the absolute pure-Never response payoff are bounded
by M*(1-nu): against opponents all choosing Never, every own response pays
zero, and otherwise the absolute contribution is at most M. This estimate
also passes to the augmented closure. It proves the AllNever conclusion.

## 4. Application to the unequal-premium calibration

Use players0,1,2,3, the native singleton matrix

    Gamma=[0,3,-1,3;2,0,1,-3;2,-2,0,-1;-1,-2,1,0],

and additive passive rewards. Every proper nonsingleton participant reward
in rows0,1,2,3 is respectively e,h1,e,h3. The native grand reward is
(10,-2,-e,-1). Assume independently

    0<e,h1,h3<=1/10.

Take S={0,1,3} and z=(9,7,0,8)/24. Direct multiplication gives

    z Gamma=(6,11,6,6)/24,

so gamma=1/4 works. Supported pair rewards are strictly positive, with
m=min(e,h1,h3). Every nonsingleton participant reward of player0 is
strictly positive, including its grand reward10. The anchor test in
Section1 therefore supplies condition3. Every native reward has absolute
value at most10, so M=10 works in the general constants.

It follows, for this ENTIRE independent-premium range, that

    max(B0,B1,B3)>=delta*(1-nu),
    max(B0,B1,B3)>=delta  on K_abs.                       (10)

In particular the hard ray(e,h1,h3)=(beta,beta/10,beta) satisfies this
conclusion for every 0<beta<=1/10. The bound depends on the fixed premiums;
no uniform positive lower bound as beta tends to zero is claimed.

For the original calibration r_i(A)=1+Z_i(A) on nonempty A, with original
live/Never zero, the source bridge is exact. Every finite deadline response
absorbs surely, so its original offer is1 plus its native offer. The native
Never offer is the limit of finite deadline offers, since own native
singletons are zero. The original Never offer is that native offer plus
1 minus opponent Never mass, and hence is at most1+B_i. Consequently

    B_i(original)=1+B_i(native),
    U_i(original)=1-nu+U_i(native).

On absorbing profiles, and their semantic closures, both vectors therefore
translate exactly by1. Equation(10) excludes the corresponding original
absorbing cap face B0=B1=B3=1; it does not shift literal Never payoffs.

The proof also allows arbitrary finite passive nonsingleton rewards: only
the singleton drift in Section1 is used, and M then enlarges as necessary.
Likewise, arbitrary finite nonsingleton participant rewards outside row0
and the supported pairs are allowed. This is a boundary-face theorem for
those broader tables, not a new UE existence class.

## 5. Strict separation from the global weighted-Quit criterion

For the displayed calibration, the older criterion asks for a probability
vector v>=0 with v Gamma strictly positive and

    K_A=sum_i v_i Z_i(A union {i})>0

on EVERY nonempty A. No such v exists throughout 0<e,h1,h3<=1/10.
Let epsilon=max(e,h1,h3). The two triple tests imply

    0<K_023=e(v0+v2)+h3*v3-2v1,       v1<epsilon/2,
    0<K_012=e(v0+v2)+h1*v1-v3,        v3<epsilon.

The positive singleton columns2 and1 then give

    v0<v1+v3<3epsilon/2,
    v2<(3/2)v0-v3<9epsilon/4.

Summing yields 1=sum v_i<21epsilon/4<=21/40, a contradiction.
Thus(10) does not merely instantiate the older globally positive
weighted-Quit test with a different weight.

## 6. What this closes and what remains

Every boundary tail in the
[incoming decomposition](CODEX_COORDINATOR__ZERO_OBSERVER_BOUNDARY_REDUCTION.md)
belongs to K_abs. For the calibration, equation(10) directly excludes its
entire face B0=B1=B3=0, including the all-zero endpoint used to produce a
first finite Never-penalty plateau. No realization of that abstract tail,
full Nash property of the incoming head, or global-minimum property of the
tail is needed. The result applies to every pivot's boundary source.

It does NOT exclude an actual global partial-Nash minimum, boundaries
with max(B0,B1,B3)>0, or penalty plateaux arising by another mechanism.
It does not make an observer-Nash head a full Nash head. In particular,
the exact partial-Nash control in the
[cap-region note](CODEX_UNEQUAL_GLOBAL__NONNEGATIVE_CAP_ROOT_ACTIVITY.md)
has strictly positive supported caps and is consistent with this theorem.

The relevant source formulas were inspected in
`quittingContinuationBestResponseValue_rootThenContinuation_eq_max`
(`UniformEquilibrium/Quitting/Root/TerminalDebtPrefix.lean`),
`quittingTerminalSemanticPair_rootThenContinuation` and
`quittingTerminalSemanticPrefix`
(`UniformEquilibrium/Quitting/Root/TerminalSemanticPair.lean`). The target
`quittingUniformEquilibriumPayoffConjecture`
(`UniformEquilibrium/Quitting/Conjecture/Basic.lean`) remains open.
No Lean command ran.

The next source question is whether the remaining boundary faces can be
excluded using the observer equalities and the inherited comparison map,
rather than an unconditional cap estimate.
