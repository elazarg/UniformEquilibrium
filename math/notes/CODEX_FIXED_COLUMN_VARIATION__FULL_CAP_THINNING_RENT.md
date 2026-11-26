# Full-cap rent under finite/Never thinning at an original minimum

## Status and question

This is supporting ordinary mathematics, not an export, a Lean theorem, or a
new uniform-equilibrium class. The question is whether a native END-active
owner can simply replace its finite law by Never at a raised original SUM
minimum. The answer is an exact observer-cap rent condition. When every END
is active, either a precise affine slope vanishes or another owner has an
END-tied response with a nonzero, quantitatively sufficient slope. No
arbitrary profile is represented as a positive-gap source.

The construction below applies to the ORIGINAL compact semantic source by
passing actual complete-law variations to a limit. Its full caps retain all
finite tests and literal Never. The absorbing endpoint supplies a positive
lower bound on the total cap curvature along the complete variation.

## 1. Source and actual one-owner operation

There are four independent private clock laws on the natural dates and a
separate Never point. All live and AllNever payoffs are zero. The native
nonempty-coalition table Z has own singleton zero. Let M bound its absolute
entries and let

    A = inf { SUM_i (B_i-U_i) : actual absorbing profiles } > 0.

The final table is r_i=theta_i(Z_i+t), with theta_i,t>0 and
Theta=SUM_i theta_i. At this fixed table the exact full SUM is

    D(P)=SUM_i theta_i(B_i(P)-U_i(P)) + t Theta nu(P),
    nu(P)=PRODUCT_i N_i(P).

Fix an ORIGINAL global minimum Y of value delta, with every original N_i>0.
Suppose owner h is native END-active, B_h=e_h, and 0<f_h=1-N_h<1.
The inverse-column graft inequality produces these hypotheses for its forced
owner h, including f_h>0, at the sources to which that argument applies.

First suppose Y is actual. Write f=f_h and let F_h be h's finite conditional
law. Keep every other law fixed, and for every q in [0,1] put

    P_h(q)=q F_h+(1-q)delta_Never.                         (1)

This is independent private randomization by h alone. It is not a common
coin selecting whole profiles. The original profile is q=f. The endpoint
q=0 is the native best-response replacement h->Never; q=1 absorbs surely.
Write H=PRODUCT_(i!=h)N_i, so nu(q)=H(1-q).

Every U_i(q) and e_i(q) is affine in q. The own cap and own Never value are
constant. In particular, throughout [0,1],

    B_h(q)=e_h(q)=B_h,
    d_h(q)=q d_h(f)/f.                                  (2)

For i!=h and every pure finite or Never test k, set

    a_i(k)=V_i(P(0);k),    b_i(k)=V_i(P(1);k),
    C_i=closure{(a_i(k),b_i(k)): k finite or Never}.

Then C_i is a nonempty compact subset of [-M,M]^2, and the FULL cap is

    B_i(q)=max_((a,b) in C_i) [(1-q)a+qb].               (3)

This includes both inequalities: each original pure test has the displayed
affine payoff, and taking the closure does not change its supremum. Arbitrary
behavioral replacements average pure tests, so no larger cap is omitted.
Consequently B_i is convex and 2M-Lipschitz on [0,1]. The whole D(q) is
convex, because every other term in D(q) is affine.

## 2. The operation belongs to the original compact carrier

No actual law representation of Y is needed. Take an actual realizing
sequence P^n with its original coordinates converging to Y. Its finite
probability f_h^n tends to f>0, so its conditional finite laws F_h^n exist
eventually. Apply (1) to each realizer using F_h^n.

Pass to a subsequence on which the finitely many endpoint U_i and e_i values
converge and each C_i^n converges in the Hausdorff metric on nonempty compact
subsets of [-M,M]^2. Such subsequences exist by compactness. The maxima in
(3) converge uniformly in q, since the affine test functional is uniformly
Lipschitz in (a,b). All endpoint prescribed and Never-response values also
converge uniformly by affinity.

For each fixed q, these are limits of ACTUAL profiles at the same final
table. Thus their semantic pairs and original N,e coordinates belong to the
same original augmented carrier. Their N_h coordinate is exactly 1-q and
the other N_i are unchanged. At q=f they recover Y: the actual original
points use q=f_h^n, and the uniform 2M-Lipschitz bounds let f_h^n be replaced
by f without changing the limit.

Equation (2) passes to the limit, including native END_h activity on the
whole path. At q=1 every approximant absorbs, so its weighted native debt
is at least theta_min A. Hence

    D(q)>=delta for every q,
    D(1)>=theta_min A,
    delta<=t Theta.                                    (4)

The last inequality uses actual AllNever at the same final table. This
argument requires neither a clock on an abstract ordered sum nor an assumed
conditional-tail minimum.

## 3. Exact price of the native best-response replacement

With only END_h assumed, the replacement q=0 gives the identity

    D(0)-delta
      = -theta_h d_h(f)
        +SUM_(i!=h) theta_i[d_i(0)-d_i(f)]
        +t Theta H f.                                 (5)

Therefore original minimality forces

    SUM_(i!=h) theta_i[d_i(0)-d_i(f)]
        >= theta_h d_h(f)-t Theta H f.                 (6)

The first term in (5) is the exact removal of h's native debt. The last
term is the exact cost of increasing ORIGINAL joint Never from H(1-f) to
H. The middle term contains the other owners' unrestricted full caps.
END_h alone supplies no upper bound on that term.

Thus a claim that native best-response replacement decreases full SUM
requires the STRICT REVERSE of (6), not just h's native payoff gain.

## 4. All-END source: affine debt plus nonnegative cap rent

Now suppose every original native END is active at q=f. For i!=h define

    g_i(q)=B_i(q)-e_i(q),
    G(q)=SUM_(i!=h) theta_i g_i(q).

Each g_i is nonnegative and convex on [0,1], because Never is offered at
every q and e_i is affine. Also g_i(f)=0. Define

    L(q)=SUM_i theta_i[e_i(q)-U_i(q)] +t Theta H(1-q).

This L is affine. If its slope is ell, then the EXACT whole-path identity is

    D(q)-delta = G(q)+ell(q-f),    G(q)>=0, G(f)=0.      (7)

Writing a prime for the slope of an affine function,

    ell = theta_h d_h(f)/f
          +SUM_(i!=h)theta_i[e_i'-U_i']-t Theta H.      (8)

In particular original minimality is precisely the family

    G(q)>=-ell(q-f),                 0<=q<=1.           (9)

If ell>0, thinning h is blocked exactly by leftward cap rent at least
ell(f-q). If ell<0, increasing h's finite mass is blocked exactly by
rightward cap rent at least -ell(q-f). If ell=0, the entire variation is
nondecreasing from its original value solely because G is nonnegative.
Convexity by itself does not reverse any of these inequalities.

## 5. Exact active-response slope alternative

Let e_i^0=e_i(0) and e_i^1=e_i(1). For (a,b) in C_i define

    l_(a,b)(q)=(1-q)(a-e_i^0)+q(b-e_i^1),
    s_i(a,b)=(b-e_i^1)-(a-e_i^0),
    A_i={ (a,b) in C_i : l_(a,b)(f)=0 }.

The compact A_i is nonempty: it includes the Never pair
(e_i^0,e_i^1), whose line and slope are zero. Since g_i is the maximum of
these affine lines, its one-sided derivatives are

    g_i'(f-)=min_(A_i) s_i,
    g_i'(f+)=max_(A_i) s_i.                            (10)

For completeness, the lower bound on the right derivative follows by using
any line active at f. For the upper bound, choose maximizing pairs at
f+epsilon, extract a convergent subsequence by compactness, and observe that
its limit is active at f. The bounded slopes then give the matching upper
bound. The left derivative is identical with signs reversed.

Combining (7), (10), and interior minimality gives

    ell + SUM_(i!=h)theta_i min_(A_i)s_i <= 0
        <= ell + SUM_(i!=h)theta_i max_(A_i)s_i.        (11)

Consequently there is a complete source-specific alternative:

* ell=0 gives the exact identity (8) with right side zero;
* ell>0 forces END-tied observer responses with negative thinning slopes,
  with total negative capacity SUM theta_i[-min_(A_i)s_i]>=ell;
* ell<0 forces END-tied observer responses with positive thinning slopes,
  with SUM theta_i max_(A_i)s_i>=-ell.

In either nonzero case at least one such observer slope has magnitude at
least |ell| / SUM_(i!=h)theta_i. Its affine response line differs from the
Never line. These are full response contacts, not selected responses used
in place of a cap.

For an ACTUAL natural-date profile, a nonzero-slope contact is attained by
an actual FINITE test. Indeed as k tends to infinity, both endpoint pure
responses tend to their native Never values by bounded convergence. Thus
the only accumulation point of distinct finite-test pairs is the Never
pair. Every point of C_i with nonzero slope is therefore one of the actual
finite-test pairs. For a compact source the same argument provides a limit
of pairs of actual full tests along the source realizers; it does not claim
an executable finite date in an unrealized compact clock.

An immediate consequence for actual profiles is useful: if every observer
has no finite response tied with END, then ell MUST vanish. This conclusion
does not assume a uniform margin between END and the cofinal finite tests.
Their possible vanishing gaps are included in the compact proof of (10).

## 6. The absorbing floor forces substantial cap curvature

Assume t Theta<theta_min A. From (4), (7), and exact cancellation of the
affine term,

    (1-f)G(0)+fG(1)
      =(1-f)[D(0)-delta]+f[D(1)-delta]
      >=f(theta_min A-delta)>0.                       (12)

Equivalently, directly in terms of full caps,

    SUM_(i!=h)theta_i[(1-f)B_i(0)+fB_i(1)-B_i(f)]
      >=f(theta_min A-delta)>0.                       (13)

Thus some observer loses END activity at an endpoint of the complete
finite/Never segment. Every END cannot remain active throughout that
segment. More quantitatively, at least one observer has cap Jensen gap at
least

    f(theta_min A-delta) / SUM_(i!=h)theta_i.

If the fixed inverse-column condition applies to every minimum on this
path, q=0 cannot itself be a minimum, by its forced positive f_h bound.
Then D(0)>delta and the inequality in (12) is strict beyond its displayed
lower bound. This uses actual original global minimality at q=0 if equality
were to hold, not a minimality assumption for an arbitrary replacement.

The curvature requirement is a consequence of the genuine source and its
absorbing gap. It is not a positive-gap example or a contradiction: the
observer full caps may have exactly this curvature.

## 7. Boundary and next question

The useful residual is now explicit. A descent by this one-owner operation
needs an upper bound violating (9), or, locally, an upper bound on the
appropriate active-response slope rent in (11). The singleton inverse
column gives END activity and a lower bound on f_h. It does not by itself
price the changes of all observer responses caused by removing h's old
finite law: those slopes also depend on the old chronology and the full
nonsingleton table.

The exact remaining question is whether the actual positive-A source can
force the required strict rent upper bound, or can force ell=0 together
with an actual interval on which all g_i vanish. A zero derivative alone
does not imply such an interval for a supremum of infinitely many affine
response lines. No interval or finite active menu is assumed here.

## 8. Source inspection and evidence limits

The bounded source lookup used the original-minimum correspondence in
`docs/FRONTIER.md` and read these declarations in place:

* `quittingTerminalDebtSumInf_eq_terminalSemanticDebtSum_of_minimum`
  (`UniformEquilibrium/Quitting/Terminal/TerminalDebtSumInf.lean`);
* `quittingStoppingLawCap_behaviorStoppingLaws_eq_continuationBestResponseValue`
  and `quittingStoppingLawCap_eq_continuationBestResponseValue_stoppingLawProfile`
  (`UniformEquilibrium/Quitting/Paths/StoppingLawOperationalDistance.lean`);
* `quittingTerminalSemanticDebtSum` and
  `quittingTerminalSemanticDebt_nonneg_of_attainable`
  (`UniformEquilibrium/Quitting/Root/TerminalSemanticDebt.lean`).

The native raise, original Never lift, properification bound and forced
inverse-column END source are proved in
[the strict inverse-column packet](../exports/FIN4_STRICT_INVERSE_COLUMN_AND_ALL_END_MINIMUM_REDUCTION.md),
Part II Sections 2--4. The raw singleton restriction is proved in Parts I
and IV of the same packet. These are canonical references after curation;
they do not record a new independent review of this note.
The existing finite/Never convex-path use in Section 17 of
[`LEAST_NEVER_MULTIPLE_BRIDGE_SOURCE.md`](../exports/LEAST_NEVER_MULTIPLE_BRIDGE_SOURCE.md)
was inspected; that argument has additional root-only/sole-bridge and
isolated-maximizer hypotheses. The present note asserts no novelty of
supremum convexity or a supplied one-coordinate variation. It records the
complete unrestricted cap-rent calculation at the current source.

No Lean files were changed, and no Lean build or new formalization check was
run. The mathematics above is supporting structure with no current
unconditional equilibrium consumer.

## 9. Weight openness and the exact zero-observer-debt obstruction

The following continuation checks the proposed uses of an open weight box.
It does not modify or promote the separately reviewed all-END source theorem.

### 9.1. What generic weights actually make common

Use independent parameters theta and lambda=t SUM theta, and define on the
same compact native augmented carrier

    V(theta,lambda)=min_Y [theta dot d(Y)+lambda nu(Y)].

This is concave and locally Lipschitz. At every point where it is
differentiable, ALL minimizing sources have the same native debt vector and
the same original joint Never probability:

    (d(Y),nu(Y))=gradient V(theta,lambda).               (14)

Indeed each minimizing vector is a supergradient of V; differentiability
makes that supergradient unique. Such parameter points have full measure in
any full-dimensional open allowed region. An open theta box with
0<t<t0 gives an open region in (theta,lambda), so the argument applies to
the actual allowed parameter family, including its small theta_h coordinate.

This does NOT give one common minimizing source as the parameters vary.
Even at a fixed parameter point it identifies only (d,nu), not the law,
payoff vector, cap vector, or response inventory.

At a differentiability point, (14) does rule out every nonconstant minimum
interval on (1): nu(q)=H(1-q) is strictly decreasing. Hence D(q)>D(f) for
every q!=f on that line. In the all-END representation (7), if ell=0 this
means G(q)>0 for every q!=f. A supremum of infinitely many affine response
lines can rise this way with derivative zero at f, so this implication does
not supply a descent direction or an interval of cap preservation.

### 9.2. Three exact observers can pin the outsider's entire finite mass

Consider a limit source produced by scaling

    theta_h=epsilon a,    theta_i=w_i for i!=h,
    t=epsilon tau,

where a,tau,w_i are fixed positive numbers in the allowed ranges. Suppose
its original native coordinates satisfy the conclusions provided by that
scaling: all N_i>0, 0<f_h<1, all native ENDs active, and

    d_i(f_h)=0 for every i!=h.                          (15)

No actual law attainment is assumed. Use the exact compact-source curve
from Section 2, keeping the old observer laws fixed. Put f=f_h and define

    beta_i = slope_q [e_i(q)-U_i(q)],       i!=h.

The affine expression vanishes at q=f by (15), so

    e_i(q)-U_i(q)=beta_i(q-f).                         (16)

If f_i=0, observer i uses original Never alone along this curve, and
beta_i=0. If f_i>0, its old finite conditional law remains an available
replacement response at every q. Its value, denoted W_i(q), satisfies

    U_i(q)=N_i e_i(q)+f_i W_i(q).

The full cap dominates BOTH e_i(q) and W_i(q). Therefore, on the ENTIRE
interval [0,1],

    d_i(q)>=max{ beta_i(q-f),
                 -(N_i/f_i) beta_i(q-f) }.             (17)

The same inequality holds in the original compact source by applying the
conditional-law identity to its actual realizers and taking the limit.
It involves genuine full-cap lower bounds from two offered replacements;
it does not replace the full cap by a restricted menu.

If beta_i!=0, the right side is strictly positive at every q!=f. In fact

    d_i(q)>=min(1,N_i/f_i)|beta_i| |q-f|.               (18)

Thus ONE observer with beta_i!=0 pins h's finite probability exactly:
there is NO different q, even arbitrarily close to f, that preserves all
three observers' zero debts while keeping their laws fixed. This is an
actual-source obstruction to the proposed removal, not an arbitrary
profile portrayed as a minimum. For nearby epsilon sources it also rules
out any fixed nonzero change of q at O(epsilon) total cost: the observer
debt in (18) stays bounded below while the original objective tends to zero.

The alternative beta_i=0 for every observer only removes this particular
obstruction. It does not establish zero observer debts away from f; their
other full responses can still make g_i(q)>0. Thus the all-END and
zero-observer-debt source conclusions alone have not produced a legal
zero-debt observer repair along (1).

### 9.3. The precise price required of an actual observer repair

Write W=SUM_(i!=h)w_i. The natural constrained limit objective is

    a d_h + tau W nu

on sources having zero debt for the other three owners. AllNever gives
the upper bound tau W; the produced limit consequently satisfies

    a d_h(Y)<=tau W[1-nu(Y)].                          (19)

Suppose one replaces h by Never AND repairs the other three laws to a
source Q with their debts again zero. The old END_h equality cannot be
carried across this repair: h's opponents have changed. Its new native debt
is exactly B_h(Q)-e_h(Q), which is merely nonnegative. A strict improvement
would require the concrete inequality

    a[B_h(Q)-e_h(Q)] + tau W PRODUCT_(i!=h)N_i(Q)
       < a d_h(Y)+tau W nu(Y).                        (20)

Zero observer debts do not bound either term on the left. In particular,
one must price h's ENTIRE repaired cap, not declare it unchanged because
its old END was active. With the observers frozen, (17) gives the exact
obstruction instead; with them repaired, (20) is the missing inequality.

This is the coherent stopping point of the weight-box continuation. The
open box yields (14), and the zero-observer limit yields (17)--(19), but
neither supplies the strict repair estimate (20). No new equilibrium
producer, excluded positive-A source class, or conjecture closure is
claimed from this continuation.

## 10. An exact Fin4 obstruction to joint observer repair after deletion

This section gives a concrete complete-table control of JOINT repair. All
three observers may replace their entire laws. The obstruction is not a
frozen-observer calculation or a finite-menu optimization. The displayed
positive-Never source is not asserted to minimize J globally; the restricted
global minimum after deleting h is computed exactly over ALL full laws.
The final paragraphs explain the compact global optimization and A=0.

### 10.1. Complete table and exact positive-Never source

Take h=0 and

    Gamma = [[ 0,-1, 1, 1],
             [ 2, 0,-1,-1],
             [-1, 2, 0,-1],
             [-1, 2,-1, 0]].

For every recipient i and every nonempty coalition S define ALL sixty native
rewards by

    Z_i(S)=0                         if i belongs to S,
           SUM_(j in S) Gamma_ij    otherwise.          (21)

Every own singleton is zero, and |Z_i(S)|<=2. Direct exact algebra gives

    det Gamma=4,
    Gamma^(-1)=(1/4)*[[4,3,1,1],
                      [4,2,2,2],
                      [4,1,3,-1],
                      [4,1,-1,3]],
    Gamma^(-1)e_0=(1,1,1,1)>0.                        (22)

Every owner independently puts probability 1/5 at date0 and 4/5 at literal
Never. A pure date0 response pays zero because every participant reward is
zero. Every later finite response and Never pays Gamma times (1/5,...,1/5),
which is (1/5,0,0,0). Thus the ENTIRE prescribed/cap/Never data are

    B=e=(1/5,0,0,0),
    U=(4/25,0,0,0),
    d=(1/25,0,0,0),
    N=(4/5,4/5,4/5,4/5),       nu=256/625.              (23)

In particular all ENDs are active, all original N are positive, h has
positive finite mass, and every observer has exactly zero FULL debt. For

    J=d_0+(1/2)nu,

the exact value is

    J=153/625 < 1/2.                                  (24)

### 10.2. Entire joint-repair correspondence after h becomes Never

Let Q be ANY actual independent complete-law profile with Q_0=Never and

    d_1(Q)=d_2(Q)=d_3(Q)=0.

All natural dates, infinite supports, literal Never, and all behavioral
replacement responses are permitted. Let S be its random first finite
coalition, with a separate empty outcome for AllNever.

Owner1 receives zero if 1 belongs to S and receives -|S| if S is a nonempty
subset of {2,3}. Hence U_1<=0. Its date0 response guarantees zero, so
B_1>=0. The equality d_1=0 implies U_1=B_1=0 and therefore

    every nonempty first coalition contains owner1, almost surely.  (25)

Compare owner2's prescribed payoff with its literal Never response. Couple
the draws of all original laws. On every event in (25), withdrawing owner2
leaves owner1 at the SAME first date. If 2 was absent, its payoff is
unchanged. If 2 was present, its old participant payoff was zero, whereas
withdrawal pays 2 for remaining coalition {1}, or 1 for {1,3}. On AllNever
the payoff stays zero. Consequently

    e_2-U_2 >= Pr(2 belongs to S) >= 0.

But e_2<=B_2=U_2, so 2 never belongs to S. The identical argument for
owner3 uses Z_3({1})=2 and Z_3({1,2})=1 and removes 3 as well. Thus

    S is either {1} or AllNever, almost surely.         (26)

This argument allows the other observers to prescribe finite clocks after
owner1's sure exit. It does not incorrectly conclude that their whole laws
must be Never. Only the first-coalition conclusion (26) is needed.

Owner0 receives -1 at {1}. A pure finite test receives either zero if it
preempts or joins that exit, or -1 if owner1 has already exited. Thus its
full cap is zero, attained at date0. With h prescribed Never,

    B_0=0,       U_0=-(1-nu),       d_0=1-nu.           (27)

For EVERY joint observer repair after deleting h,

    J=1-nu/2 >=1/2.                                   (28)

AllNever attains 1/2, so (28) is the EXACT restricted global minimum over
all actual full laws with h Never and zero observer debts. Combining (24)
and (28), every such joint repair increases J by at least

    1/2-153/625=319/1250.                              (29)

This is a falsifier of a broad deletion-and-repair lemma assuming only
own-zero rewards, a strict positive inverse column, all-END activity,
positive original Never, positive h finite mass, and zero observer debts.
It does not falsify a statement with the additional A>0 or original-global-
minimum hypothesis at the particular source (23).

### 10.3. The restricted lower bound survives the original compact closure

The bound is not an artifact of requiring exact finite-date laws. Here is a
quantitative check that also avoids transferring a pathwise property to a
semantic limit without proof.

First take any actual Q with h Never, allowing positive observer debts.
Let p_bad be the probability of a nonempty first coalition omitting1.
The same payoff argument gives

    p_bad <= d_1.

On good events containing1, withdrawing observer2 gains at least1 whenever
2 participates. On bad events the payoff change has absolute value at most4,
because M=2. Therefore

    Pr(1,2 both belong to S) <= d_2+4d_1,
    Pr(1,3 both belong to S) <= d_3+4d_1.

Consequently the probability of any nonempty first coalition other than
{1} is at most

    eta=9d_1+d_2+d_3.

Owner0's Never payoff differs from -(1-nu) by at most3 eta. Every finite
test pays at most2 on the exceptional first-coalition event and at most0
otherwise, while its date0 test pays0. Hence

    |U_0+(1-nu)|<=3 eta,      0<=B_0<=2 eta.            (30)

Now let a point of the ORIGINAL augmented compact carrier satisfy N_0=1
and d_1=d_2=d_3=0. On its actual realizing sequence, redirect owner0's finite
mass to Never. That mass tends to zero, and the uniform 2M coupling bounds
preserve the prescribed values, every full cap, and all original N limits.
Apply (30) to these actual h-Never laws and take the limit. This proves
(27) exactly at the compact point as well. Thus the restricted compact
global minimum is also precisely 1/2.

### 10.4. Honest A=0 and the unrestricted compact minimum

The table (21) has A=0; it is not a hypothetical counterexample. To see
this using an inspected existing producer, raise every nonempty reward by
one. At R=Z+1 every participant receives exactly its own singleton1.
Thus every absorbing product root has an active player whose forced-Quit
payoff equals its own singleton. This supplies
`HasProductLowQuittingPremium`, and
`exists_uniformEquilibriumPayoff_of_productLowPremium`
(`UniformEquilibrium/Quitting/Classification/Existence/ProductLowPremiumUniformPayoff.lean`)
produces a uniform payoff for R. Its hypotheses and the product-low
definition in
`UniformEquilibrium/Quitting/Classification/ProductLowQuittingPremium.lean`
were read in place; no new Lean check is claimed.

The inspected terminal-gap equivalence gives actual profiles with

    D_R=D_Z+4nu ->0.

Redirecting a least-Never owner's Never mass to a finite date gives actual
absorbing profiles with native debt at most D_Z+14M nu^(1/4), which tends
to zero. Hence A=0. An absorbing approximating sequence has an original
compact limit with d=0 and nu=0. Therefore the UNRESTRICTED compact
constrained problem (zero observer debts, no requirement N_h=1) has global
minimum J=0. Its restricted h-Never minimum remains 1/2 by (30).

These are two exact global value calculations on the ORIGINAL compact
carrier. They show a genuine separation of the constrained global optimum
from every deleted-h observer repair. The explicitly realized positive-
Never point (23) demonstrates the same repair obstruction before reaching
the global optimum, but is not itself that optimum.

For general own-zero tables, the same logic proves a useful scope warning:
for a,b>0, the minimum of a d_h+b nu over the compact zero-observer-debt
fiber is zero if and only if A=0. One implication uses absorbing
approximants. Conversely, a compact zero-debt point with nu=0 can be
properified along its actual realizing sequence to give A=0. Accordingly,
an explicit POSITIVE global constrained compact minimum would already
require A>0. A positive example over only ACTUAL exact-observer laws would
instead have to exploit the possible difference between taking closure
before or after imposing the exact observer equations.

## 11. Whole proper-clock paths admit connected exact observer repair

This section is ordinary mathematics, internal and not independently
reviewed. It is an unconditional continuation result on the proper-clock
domain, followed by its exact limitation for the positive-A constrained
source. It assumes neither an actual global minimizing law nor a selected
continuous equilibrium section. No new table is constructed.

The proof below transports finite-dimensional connected continuation to all
complete observer laws along an arbitrary weakly continuous path of proper
pivot clocks. It supplies neither a continuous equilibrium section nor a
component through a prescribed endpoint equilibrium.

### 11.1. The spanning-continuum theorem

Let X=N union {Never} carry its one-point compactification, and let P(X)
carry the weak topology. Fix a bounded quitting table, an owner h, and a
weakly continuous path

    q_h : [0,1] -> P(X),     q_h(a)(Never)=0 for EVERY a.

For each a let E(a) be the triples of complete independent observer laws
whose three FULL behavioral debts against q_h(a) are zero. Then the graph

    G={(a,x): a in [0,1], x in E(a)}

contains a nonempty compact connected subset K whose parameter projection
is ALL of [0,1]. In particular K meets both endpoint fibers. This does not
assert that K contains any prescribed equilibrium at either endpoint, or
that its fibers are singletons, or that it is the graph of a section.

Here is a proof retaining the unrestricted cap tests. Put

    rho_L=sup_a Pr_{q_h(a)}(T_h>=L), including Never.

For each L the tail probability is continuous in a, since its complement
is a finite clopen set of X. These functions decrease pointwise to zero.
Dini's theorem on [0,1] gives rho_L->0. Thus the family of proper h clocks
is uniformly tight. No uniform hazard or common bounded support is needed.

For an observer, changing any reply at a date at least L to Never changes
its payoff by at most 2M rho_L, uniformly in the other observer laws and
in a: the unchanged h clock has already absorbed on the complementary
event. The same screening shows that ALL prescribed payoffs and each
observer's full cap and debt are jointly continuous in (a,x). Indeed they
are uniform limits of finite-head calculations; for a cap the error is
uniform over every replacement, not just over the prescribed law.

For each L restrict the three observers to {0,...,L-1,Never}, keeping the
whole original q_h(a). This is a continuous finite-game family. The usual
Browder continuation theorem applied to its continuous Nash fixed-point
map gives a compact connected subset K_L of its Nash graph meeting both
endpoint fibers. Its points have FULL observer debts at most 2M rho_L.
Embed all these graphs in the SAME compact metric space

    [0,1] times P(X)^3.

Compactness of the nonempty compact-set hyperspace gives a subsequence
converging in Hausdorff distance to a nonempty compact K. A Hausdorff
limit of compact connected sets is connected, and its parameter projection
still contains both endpoints and therefore the whole interval. Joint
continuity of the observer debts and rho_L->0 put K inside G. Every point
of K consists of actual complete laws, and the original h clock makes the
prescribed profile absorb surely. This finishes the proof.

The finite-dimensional input is exactly the standard continuation form:
for a continuous map f:[0,1] times C -> C on a nonempty finite-dimensional
compact convex C, its fixed-point graph has a connected component meeting
both endpoint fibers. The Nash map on the product of the finite mixed
strategy simplexes supplies this f. No infinite-game fixed-point or
connectedness theorem is silently substituted for the limiting argument.

### 11.2. The precise deleted-cap continuity condition

Now assume native own zero for h. Its prescribed payoff U_h is continuous
on G by the same h-clock screening. Its FULL cap B_h is independent of
its own clock and is only lower semicontinuous in the observer laws.
For an arbitrary finite deadline t, V_h(t;x) is continuous in x because
it depends on finitely many opponent coordinates. Native own zero gives

    V_h(t;x) -> e_h(x) as t->infinity,
    B_h(x)=sup_{t finite} V_h(t;x).

The first statement is pointwise for each fixed x; it supplies no uniform
limit on K. Define the continuous finite-query caps

    b_L(x)=max_{0<=t<=L} V_h(t;x).

They increase pointwise to B_h. Consequently, on the compact continuum K,

    B_h is continuous
      iff sup_{(a,x) in K} [B_h(x)-b_L(x)] -> 0.       (31)

The forward implication is Dini; the reverse is uniform convergence of
continuous functions. This is an exact equivalence, not an imposed bound
by the h clock's tail. It identifies the missing uniform full-response
control for any cap intermediate-value argument along this continuum.
Under (31), d_h=B_h-U_h is continuous, so its image on K is an interval.
Without (31), connectedness alone does not supply that conclusion.

For an explicit own-zero native table, for every nonempty coalition S set

    Z_i(S)=1_{0 in S}                         for i=1,2,3;
    Z_0(S)=3                                 if 1 in S;
           1                                 if 1 notin S, 2 in S, 0 notin S;
           0                                 otherwise.

These disjoint rules specify all sixty coordinates. Curation relocates
this table from Section 3 of Git path
`b8d49627:math/notes/CODEX_NATIVE_DYNAMICS__FIXED_CLOCK_EXACT_REPAIR_AND_DELETED_TAIL.md`;
it does not claim a new example or export review.
Fix the h=0 clock delta_1, observer 1 law p delta_1+(1-p)Never,
observer 3 Never, and 0<p<1. For n>=2 put
a_n=1-1/(n-1). At parameter a_n let observer 2 use delta_n, interpolate
linearly between delta_n and delta_(n+1) on [a_n,a_(n+1)], and use Never
at parameter 1. This is a weakly continuous path of complete laws.
At every parameter the three observer debts are exactly zero, since their
prescribed payoff is the maximum possible value 1. Along the path,

    U_h=3p everywhere,
    B_h=1+2p for a<1,       B_h=3p for a=1.          (32)

To verify the full cap, the event that observer 1 quits at date 1 pays h
at most 3 and has probability p. Otherwise, waiting beyond observer 2's
proper finite clock earns 1 before the endpoint; no response can do
better. At the endpoint that clock is Never, so no such extra payoff is
available. All finite replies and Never are covered by these bounds.
For every fixed L, choosing n>L makes all first L queries miss the extra
1-p, which is the uniform failure in (31).

Thus even a weakly continuous path of ACTUAL exact observer equilibria,
with an unchanged bounded proper h clock, can have a two-point cap image.
This reuses the prior table and strengthens its sequential discontinuity
observation; it is not a new calibration. The full equilibrium graph of
that example has other paths. Hence (32) does NOT refute existence of a
better chosen continuum or selector, nor does it satisfy positive A.

### 11.3. Boundary of the constrained positive-A application

For any proper h clock and any x in E(a), the actual profile absorbs and
all observer debts vanish. Therefore its remaining debt satisfies

    d_h>=A.                                         (33)

This holds on every continuum above. In contrast the compact constrained
problem C={d_j=0 for j!=h}, J_r=d_h+r nu has m(r)<=r by AllNever.
If 0<r<A, every constrained sublevel J_r<=r obeys the retained original
properification estimate

    A<=d_h+14M nu^(1/4)<=r+14M nu^(1/4),
    nu>=((A-r)/(14M))^4.                             (34)

This calculation also holds on the ORIGINAL augmented compact carrier:
apply properification to actual realizers, allow their observer debts to
tend to zero, and pass the retained numerical limit. It does not identify
a weak limit of actual laws with an attained compact minimizer. Since
every N_i>=nu, this low-objective sublevel stays uniformly away from ALL
proper-clock faces in the retained original-N coordinates.

A weakly continuous path of proper clocks may converge to an improper
clock, but uniform tail tightness then fails at that endpoint. Neither the
observer-cap continuity proof in 11.1 nor its exact Nash-graph limit
extends across that endpoint by this argument. Original Never mass is not
weakly continuous there. Nor can the spanning theorem be anchored at a
compact constrained source that has not been realized by actual laws.

Accordingly connected observer repair is available throughout the proper
domain, while its whole graph lies above the absorbing floor (33). A
source-specific continuation to it still needs endpoint realization and
the deleted-cap control (31), together with an original objective account
that crosses (34). Strict positivity of Gamma^(-1)e_h does not supply
these steps in the argument above. This is a completed graph theorem and
a precise cap/boundary obstruction, not a positive-gap exclusion.

Original verification: the checker at Git path
`b8d49627:math/experiments/CODEX_NATIVE_DYNAMICS__FIXED_CLOCK_DELETED_TAIL_CHECK.py`
passed its 144 clock/offset cases. An inline Fraction calculation using its
full-payoff and full-cap routines also checked 36 adjacent-date
interpolations in (32); no new checker file was created. The general
continuum theorem is the proof above, not an inference from those finite
checks. Documentation validation passed at that time. No Lean command,
export, shared-index or git edit was performed in that research step.
Curation preserves this execution record and claims no new check.
