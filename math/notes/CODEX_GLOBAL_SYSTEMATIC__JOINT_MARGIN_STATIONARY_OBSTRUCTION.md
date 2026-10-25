# All four observer-margin tests can pass without a stationary equilibrium

Owner: CODEX_GLOBAL_SYSTEMATIC. Complete ordinary-mathematical control with
an exact rational interval check; review status is recorded in the
accompanying feedback. Not a Lean result or an export. The game has an explicit uniform equilibrium, so this
is an obstruction to a proposed case split, not a counterexample to Fin4.

Joint positivity of the four raw capacities in the
[observer-margin theorem](CODEX_GLOBAL_SYSTEMATIC__TERMINAL_OBSERVER_MARGIN.md)
does NOT force a stationary approximate-equilibrium family or an absorbing
exact finite-calendar equilibrium. The rational table below has neither,
even though it passes basic singleton-source screens. A period-three profile
is an absorbing exact Nash equilibrium and a uniform equilibrium.

## 1. All sixty original rewards

Players are 0,1,2,3. Core labels 1,2,3 are cyclic, with next and prev read
modulo three. Define native numbers Z on every nonempty coalition A, then
set ORIGINAL rewards r_i(A)=1+Z_i(A). Original live and AllNever rewards
remain zero. Thus every original own singleton is1.

For player0:

    Z0(A)=1 if 0 is absent;
           9/4 if A=I;
           0 otherwise.

For core owner i absent from A:

    Z_i(A)=-1/100 if 0 belongs to A;
           -16*1_(next(i) in A)+32*1_(prev(i) in A) otherwise.

For core owner i belonging to A:

    Z_i({i})=0;
    Z_i({i,next(i)})=-15;
    Z_i({i,prev(i)})=30;
    Z_i({1,2,3})=17;
    Z_i(A)=99/100 if 0 belongs to A and A!=I;
    Z_i(I)=-101/100.

These disjoint rules exhaust all sixty coordinates. Native own singletons
are zero. The native singleton matrix is

    Gamma=[0,1,1,1;
           -1/100,0,-16,32;
           -1/100,32,0,-16;
           -1/100,-16,32,0].                              (1)

Every column has a negative entry, and exact multiplication gives

    det Gamma=1344/25,
    Gamma^(-1)e0=(1600,1,1,1)/3,
    Gamma*(800,1,1,1)=(3,8,8,8).                           (2)

Gamma is also R0: if z>=0, Gamma z>=0 and z_i(Gamma z)_i=0, any positive
core coordinate forces z0=0 by row0. A one-owner core support has a negative
outsider coordinate; a two-owner support has nonzero reciprocal entries
and cannot satisfy both active equalities; full core support contradicts
the invertibility of its block (determinant 7*16^3). A pivot-only support
violates the negative column0. Thus z=0. These facts do not constitute a
claim that every known counterexample-source condition is satisfied.

## 2. Every raw margin capacity is strictly positive

Write A_i^p=Z_i(I\{p})-Z_i(I\{p,i}) for i!=p, and
C_i=Z_i(I)-Z_i(I\{i}). These differences are identical for original r.
Here

    C=(5/4,-1,-1,-1).

For pivot0, all three A_i^0=1, so Lambda0=1. For any core pivot p, the
other core observers have A_i^p=1 and player0 has A_0^p=-1. Hence

    Lambda_p=max_(x in[0,1]) min(-1+9x/4,1-2x)=1/17,
    attained at x=8/17.                                  (3)

The tests therefore have strict positive margins for all four pivots.

## 3. No exact Nash root can have a sure quitter

Let q=(x,q1,q2,q3) be a product root and H_i=product_(j!=i)(1-q_j).
Let Delta_i=Q_i-P_i be its native Quit-minus-Continue difference with
zero continuation. Direct expansion of the table gives

    Delta0=-(1-H0)+(9/4)q1 q2 q3,
    Delta_i=(1-x)(q_next-2q_prev+2q_next q_prev)
                   +x(1-2q_next q_prev),  i=1,2,3.       (4)

At native continuation v the exact root gap is Delta_i-H_i v_i.
For an original continuation cap B, the same formula applies with v=B-1:
forced Quit adds1, while Continue adds1-H_i+H_i B_i. Every actual original
cap B0>=1, because Quit0 gives player0 at least1. Consequently v0>=0.
We prove that no Nash root exists with any q_i=1 and v0>=0, with no
restriction on the other continuation coordinates.

If x=1, the three core gaps are 1-2q_next q_prev. Their COMPLETE Nash
census consists of permutations of (0,1,1), permutations of (1,1/2,1/2),
and (1/sqrt2,1/sqrt2,1/sqrt2). Indeed a zero core hazard forces both others
to1; with all positive, two sure hazards are impossible, one sure hazard
forces the other two to1/2, and otherwise all pair products equal1/2.
For these three types player0's gap is respectively at most

    -1,       -7/16,       3/2-19/(8sqrt2)<0.

Thus player0 cannot be sure.

Suppose a core owner i is sure. Put a=q_next(i), b=q_prev(i). If x=0,
the prev owner's gap is1, forcing b=1, and the next owner's gap is3b-2=1,
forcing a=1. Player0 then has positive gap5/4, contradiction. Since x=1
was excluded, we have 0<x<1. Player0's indifference now gives ab=4/9.
The other two core gaps, with continuation coefficients zero, are

    G_next=(1-x)(3b-2)+x(1-2b),
    G_prev=1-2xa.                                       (5)

If a=1, then b=4/9 and G_prev=0 forces x=1/2; the sure next owner then
has gap -5/18. If b=1, then a=4/9 and G_next=0 forces x=1/2; the originally
sure owner i has gap -5/18. These unit cases fail. Otherwise both a,b are
interior; (5) and ab=4/9 imply

    x=1/(2a),       36a^2-51a+20=0.

The quadratic discriminant is -279. This excludes every remaining case.

Any absorbing finite-calendar profile has a first reached root with a sure
quitter: at least one private law is proper and has finite support. In an
exact terminal Nash profile its root is Nash against an actual continuation
cap, by the complete cap/debt recursion, even if the all-Continue branch
has probability zero. The preceding census therefore excludes EVERY
absorbing exact finite-calendar equilibrium of the original game.

## 4. No absorbing stationary equilibrium

A stationary profile repeats fixed hazards q at every date. With at least
two positive hazards, every player's opponents absorb almost surely, even
under an arbitrary unilateral replacement. Every original response payoff
is then exactly1 plus its native response payoff. Thus Nash comparison is
unchanged by the row shift.

For native forced-Quit value Q_i, passive current value P_i and opponent
survival H_i, a necessary stationary Nash condition has the sign of

    F_i=(1-H_i)Q_i-P_i.                                  (6)

Specifically F_i<=0 at q_i=0, F_i=0 at 0<q_i<1 and F_i>=0 at q_i=1.
To derive (6), the native stationary value is
[q_i Q_i+(1-q_i)P_i]/[1-(1-q_i)H_i]; multiplying its Quit-minus-Continue
gap by the positive absorption denominator yields (6).

A solo stationary owner is also impossible. For core owner j, take the
observer i with next(i)=j. Its Never native payoff is -16, while Quit0
pays -15q_j>-16. For solo owner0, any core observer's corresponding offers
are -1/100 and (99/100)q0. These improvements survive the original row
shift because each such observer faces a proper opponent. AllNever is
not absorbing (and is not original Nash because own singletons are1).

Section3 excludes every stationary sure hazard. Suppose first x=0 and
some core activity remains. If a core hazard is zero, there is a core row
with next hazard a>0 and prev hazard zero. Its gain is a(16-15a)>0. It
would have to quit surely, contradicting Section3. Thus all three core
hazards are interior.

For a=q_next, b=q_prev, stationarity is equivalent to

    2b-a=T(a,b),
    T(a,b)=2ab[1-(1-a)(1-b)]/[1+15(1-a)(1-b)].            (7)

T is symmetric and strictly increasing in both positive arguments. The
three cyclic equations force all hazards equal. For completeness, cyclically
relabel so q1 is smallest. If q1<=q2<=q3, monotonicity gives
T(q3,q1)>=T(q1,q2), hence 3q1>=2q2+q3. If q1<=q3<=q2 instead,
T(q1,q2)<=T(q2,q3), hence 3q2<=q1+2q3. Either inequality forces equality
of all three coordinates.

Their common q obeys

    1+15(1-q)^2=4q^2-2q^3.

The left side decreases and the right side increases on[0,1]. At q=4/5
the two sides are 200/125 and192/125, so the solution has q>4/5. Player0's
Never payoff is1, whereas its Quit0 offer is(9/4)q^3>144/125>1. This
contradicts its prescribed Continue action.

It remains that x>0 and some core hazard is positive. All hazards are
nonsure. Player0's Never native payoff is1, so its mixing condition is

    q1 q2 q3=4/9.                                        (8)

All four hazards are now interior. Put v=1-x, a=q_next and b=q_prev.
For a core row,

    H=v(1-a)(1-b),
    P=16v(-a+2b)-(1-v)/100,
    Delta=v(a-2b+2ab)+(1-v)(1-2ab),
    F=(1-H)Delta-H P.                                   (9)

The exact rational checker
[`CODEX_GLOBAL_SYSTEMATIC__JOINT_MARGIN_STATIONARY_CHECK.py`](../experiments/CODEX_GLOBAL_SYSTEMATIC__JOINT_MARGIN_STATIONARY_CHECK.py)
excludes simultaneous zero of these three gains on the CLOSED domain

    v in[0,1], a,b in[4/9,1], c=4/(9ab)<=1.              (10)

It uses the identity, with h=(1-a)(1-b),

    F=C+v B-v^2 D,
    C=1-2ab,
    B=a-2b+4ab-1-hC+h/100,
    D=h(-15a+30b+4ab-1+1/100).                           (11)

The three expressions are F(a,b,v), F(b,c,v), F(c,a,v). Thus the adapter
from every remaining stationary profile to the checked domain is literal.

Every interval endpoint and operation in the checker is a Python Fraction.
It starts with the box in(10), removes ab<4/9 boxes as infeasible, intersects
the derived c interval with c<=1, and discards a box only when some gain's
rational interval excludes zero. Otherwise it bisects a widest coordinate
into two covering closed halves. Exhaustion after9589 boxes proves that the
whole domain is excluded. An unresolved small box is a hard failure, not
an accepted certificate. No floating arithmetic, numerical root search,
saved box dump or external solver is a mathematical input.

Reproduction: run `python math/experiments/CODEX_GLOBAL_SYSTEMATIC__JOINT_MARGIN_STATIONARY_CHECK.py`.
It prints `EXACT RATIONAL PASS: no simultaneous zero; boxes 9589`.
This completes the absorbing stationary exclusion.

### A positive regret floor for every stationary profile

The exclusion is stronger than absence of exact stationary Nash. For every
stationary hazard vector q, let rho(q)=max_i(B_i(q)-U_i(q)) be its original
terminal regret against all behavioral deviations. There is a constant
eta>0 such that rho(q)>=eta for every q in[0,1]^4.

Otherwise take rho(q_n)->0 and a convergent subsequence q_n->q*. If q* has
at least two positive coordinates, every player still faces a proper
opponent near the limit. Its prescribed value, Quit0 offer and Never offer
are continuous there. Both endpoint offers must be at most its limiting
prescribed value. Against stationary opponents the prescribed value is a
convex combination of these two offers, and every finite deadline offer
lies between them. Thus q* would be an exact stationary Nash profile,
contradicting the exclusion above. If q* has exactly one positive coordinate,
the explicit solo-observer improvement proved above remains strictly
positive by continuity of that observer's values and offers. This is also
impossible.

It remains q*=0. The zero vector itself has regret at least1, so discard
zero terms and put s_n=sum_i q_ni>0. Along a further subsequence,
alpha_n=q_n/s_n converges to alpha>=0 with sum_i alpha_i=1. First-order
expansion of the stationary absorption numerator and denominator gives

    U_i(q_n) -> 1+(Gamma alpha)_i.

Forced Quit0 converges to1; vanishing regret therefore gives Gamma alpha>=0.
For every i with alpha_i<1, opponents have positive total hazard eventually,
and their original Never offer converges to

    1+(Gamma alpha)_i/(1-alpha_i).

Its comparison with U_i gives alpha_i(Gamma alpha)_i<=0, hence equality.
If alpha_i=1, equality follows directly from Gamma_ii=0. Thus alpha is a
nonzero complementary solution of Gamma alpha>=0, contradicting the R0
property proved in Section1. This proves the uniform positive regret floor.
In particular stationary profiles cannot provide uniform epsilon equilibria
for arbitrarily small epsilon: for each fixed stationary profile, any
strictly profitable terminal deviation persists at sufficiently long finite
horizons. No analogous approximate exclusion is claimed here for arbitrary
finite-calendar profiles.

## 5. An explicit infinite-periodic equilibrium and the exact limitation

Let player0 Never. In chronological order the only eligible core quitter
cycles1,2,3,1,2,3,..., with hazard1/2 on its own turn. Every other owner
Continues at that date. The native continuation vector at a turn of owner1
is

    (1,0,16,0),

and the corresponding vectors rotate the core coordinates. At its own
turn the mover has both endpoints0. The owner whose current passive reward
is -16 has Continue value0 and joining offer -15/2; the owner whose passive
reward is32 has Continue value16 and joining offer15. Player0 has Continue
value1 and joining offer0. All complete deviations therefore respect the
specified continuation caps: iterate these one-stage inequalities, and
use opponent absorption to make the bounded remaining term vanish.

Deleting any one player's prescribed clock still leaves at least two core
hazards1/2 every three dates. Opponent survival after3n dates is at most
4^(-n), uniformly over the deviator's complete replacement. Thus absorption
is sure and each response payoff shifts by1 in the original game. Its
initial payoff and full-cap vector are exactly

    (2,1,17,1).

The same fixed profile is a uniform equilibrium. The uniform geometric
opponent-survival bound bounds expected absorption time, including every
unilateral deviation; finite-horizon average values converge uniformly to
the terminal values. The payoff target is fixed before the requested error.

The countercontrol therefore leaves two different arbitrary-table branches:
Lambda_p<=0 forces a Never-active observer at that pivot's augmented
partial-Nash sources; all Lambda_p>0 still permits genuine dynamic games
with no stationary approximation or finite-calendar exact solution. Further reward data
or a nonstationary construction are required in the second branch. This
example does not refute UE existence or every possible use of joint margin
positivity. The uncontrolled lower-coalition joining gaps here include
one -2 entry in every pair of core owners.
