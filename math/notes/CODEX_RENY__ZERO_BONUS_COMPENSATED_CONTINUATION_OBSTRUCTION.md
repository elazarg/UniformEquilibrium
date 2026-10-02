# Zero-extra-bonus continuation fails uniformly over finite menus

Author: CODEX_RENY.

Ordinary mathematical proof draft, not checked in Lean. The all-menu
lower bound and its conditioning argument await independent review.
The positive-bonus comparison branch is previously independently reviewed
mathematics, reproduced here with its global pivot certificate.

This is a counterexample to removing the EXTRA Never bonus from the
late-cap-compensated selector, even after arbitrary finite menu enlargement
and complete reselection. It is not a counterexample to the intended rule
which allows arbitrarily small POSITIVE bonus ceilings.

## 1. Exact question and result

For a finite deadline N and bonus ceiling η≥0, let c_N(η) be the minimum
original full repair value over ALL compensated fixed points and ALL
bonus vectors β∈[0,η]³. The exact finite correspondence is defined below;
in particular its pivot must globally minimize the ORIGINAL unrestricted
repair objective. It is not merely a best response for its own payoff.

For the single rational reward table in Section 2, the following hold:

    c_N(0) ≥ 1/32                         for every N≥1;       (1)

    c_(3K)(η) ≤ 8^(−K)                    if η≥4^(−K), K≥1.   (2)

Consequently

    inf_(N≥1) c_N(η)=0                    for EVERY η>0,
    inf_(N≥1) c_N(0)≥1/32,

    lim_(η↓0) inf_(N≥1) c_N(η)=0
                  < inf_(N≥1) c_N(0).                      (3)

The quantifier in (1) covers every global pivot optimizer, every
nonpivot support, every closed geometric-tail boundary point, and every
finite menu. No symmetry restriction is imposed on the chosen laws.

One precise proposed continuation principle is therefore false:

    There is a function ω(η)→0 as η↓0 such that, for every menu N
    and every compensated fixed point with β∈[0,η]³ and value L,
    some larger finite menu N'≥N admits a zero-extra-bonus
    compensated fixed point with value at most L+ω(η).         (C)

This fails even if the endpoint can be selected afresh, without any
connectedness or proximity requirement. In particular connectedness
alone cannot supply the asserted value orientation. The proof makes no
claim that the entire parameterized fixed-point set is disconnected.

## 2. Game, behavioral responses, and the closed repair domain

Players are I={0,1,2,3}; player 0 is the pivot. Players 1,2,3 have cyclic
predecessor and successor in that order. For every nonempty S⊆I put

    r_0(S)=1                           if 0∈S;
           2                           otherwise.

    r_j(S)=0                           if j∈S;
           −1                          if j∉S and 0∈S;
           2·1_(pred(j)∈S)−1_(succ(j)∈S) otherwise, j=1,2,3.

This specifies ALL rewards, has bound 2, and has own singleton vector
(1,0,0,0). It is the canonical VANISH fixture, not a new reward table.

Each player independently samples a stopping law on ℕ∪{Never}.
The first finite date pays the coalition of all players stopping then;
all Never pays zero. Before absorption the only observed history is
all-Continue. Thus complete unilateral behavioral replacements have the
payoffs of stopping laws, and their caps are the suprema over all pure
finite dates and Never. Write U_i for prescribed payoff, B_i for the
full cap, d_i=B_i−U_i, and E=max_i d_i. There is no shared randomization,
observation of hidden plans, transfer in the original game, or detection
of a unilateral deviation.

Fix N≥1. Nonpivots choose laws p_j on F_N={0,…,N−1,Never}. Put

    z_j=p_j(Never),     D=z_1 z_2 z_3,
    D_j=∏_(k∈{1,2,3}\{j}) z_k.

The pivot's compact convex mass domain is

    m=(x_0,…,x_(N−1),λ,ν,α),
    x_t,λ,ν≥0,    Σ_(t<N)x_t+λ+ν=1,    0≤α≤λ.             (4)

Here λ is late FINITE mass, ν is Never mass, and α is the first late
atom. If 0<α≤λ, its literal tail has atoms

    μ_0(N+k)=α(1−α/λ)^k,       k≥0.

The geometric rate α/λ belongs to the conditional finite component,
not to the whole tail when ν>0. The face α=0<λ is a closed repair point,
not such a literal stopping law.

For this particular table, however, EVERY closed point has exactly the
same U and full cap vector as the finite pivot law

    μ_0^*=Σ_(t<N)x_tδ_t+λδ_N+νδ_Never.                    (5)

Indeed r_j({0,j})=0, so moving α changes no nonpivot late endpoint;
all prescribed and old-menu response payoffs are independent of α too.
Thus no approximate realization or fictitious payoff is needed here.

More explicitly, let Q_t be the pivot's pure response at t<N and W_0
its Never response. Its cap and payoff are

    B_0=max({Q_t:t<N}∪{W_0,W_0+D}),
    U_0=Σ_(t<N)x_t Q_t+λ(W_0+D)+νW_0.                    (6)

For j≠0 let π_j,t be its pure response at t<N against (5), and A_j
the contribution from absorption strictly before N when j chooses Never.
The Never and first-late endpoints are

    W_j=A_j−D_jλ,       C_j=A_j,
    U_j=Σ_(t<N)p_j(t)π_j,t+z_j W_j,
    B_j=max({π_j,t:t<N}∪{W_j,C_j}).                       (7)

All late pure response values for a geometric tail lie between W_j
and C_j; for (5), the response at N is C_j and later responses are W_j.
Define L(m,p)=max_i(B_i−U_i), using (6)–(7). It is independent of α,
nonnegative, and equals the actual unrestricted E of (5). For fixed p
it is a finite maximum of affine functions of m. The existing exact
geometric-repair theorem identifies its minimum with the infimum over
ALL pivot stopping laws, not only finite or geometric laws.

## 3. The original compensated correspondence

For a fixed β∈[0,η]³ define

    Δ_j=D_jλ,
    m∈argmin_(m' satisfying (4)) L(m',p),
    p_j∈argmax_(q_j∈Δ(F_N))
          {U_j(m,q_j,p_−j)+(Δ_j+β_j)q_j(Never)}.         (8)

The pivot minimizes original FULL regret. The nonpivot subsidies are
auxiliary synthesis objectives only. Each Δ_j depends on opponents and
pivot coordinates, never on the responding player's candidate q_j.

For completeness, these sets are nonempty at every N and β. Each
nonpivot's auxiliary payoff is continuous and affine in its own law;
the original objective L is continuous and convex in m for fixed p.
The individual argmin and argmax correspondences on
fixed compact convex domains are nonempty, compact, convex-valued, and
upper hemicontinuous. Kakutani gives a fixed point. Their joint graph
is closed also as β varies. Hence the set of all such points with
β∈[0,η]³ is compact and nonempty, and c_N(η) is attained. Compactness at
a fixed N is not asserted uniformly over increasing menus.

At β=0 the auxiliary Never value is W_j+Δ_j=C_j. Therefore the
maximum auxiliary pure value equals the ORIGINAL FULL cap B_j in (7).
At a fixed point the auxiliary expected payoff equals that maximum, so

    d_j=B_j−U_j=z_jΔ_j=λD             for j=1,2,3.       (9)

At a global pivot minimizer, d_0 cannot strictly exceed all the other
debts. Otherwise mix m slightly toward a pure pivot full best response,
available among the finite endpoints in (6). The pivot cap stays fixed,
its debt strictly decreases, and all finitely many other gain functions
remain strictly below the old maximum by continuity. This contradicts
global minimization. This argument also works on the closed boundary.
Combining it with (9) gives the exact identity

    L=λD,          d_0≤λD.                               (10)

## 4. Zero value is impossible; every relevant row is reached

We first prove directly that this table has no exact full behavioral
Nash profile with every stopping law finitely supported. This avoids
importing either a subgame-perfect selection assumption or a complete
finite-menu equilibrium classification.

The three-nonpivot product row with continuation zero has Quit value 0
and Continue values C_j=2q_pred(j)−q_succ(j). Its only Nash row is q=0.
For if q_m=max_j q_j>0, then C_succ(m)≥q_m>0, forcing
q_succ(m)=0. Since m uses Quit, C_m=2q_pred(m)≤0, so q_pred(m)=0.
But then C_pred(m)=−q_m<0, forcing q_pred(m)=1, a contradiction.

Suppose a finite-support full Nash profile had a positively reached row
with certain absorption. A product row has certain absorption only if
some player quits surely. If a nonpivot quits surely, the pivot strictly
prefers Continue (payoff 2) to Quit (payoff 1). With the pivot continuing,
each nonpivot can compare its prescribed row payoff with Quit now and
with Continue now followed by Quit at the next integer date. The latter
replacement pays zero on the current all-Continue branch: at the next
date every absorbing coalition contains the deviating player. The row
is reached with positive probability, so both are legal profitable-
deviation tests if their conditional gains are positive. Prescribed
absorption is certain, so the comparisons imply exactly the three-player
zero-continuation row Nash conditions, contradicting the preceding lemma.

If instead the pivot quits surely, every nonpivot strictly prefers Quit
(0) to Continue (−1), forcing all three to quit; then the pivot would
strictly gain by Continue. This is again impossible. These arguments
do not inspect a strategy at an unreached continuation.

It follows inductively that no row through the largest finite support
date has a sure quitter and all four Never masses are positive. Moving
only the pivot's Never mass to a later finite date gains exactly νD>0,
because it changes nothing unless all three nonpivots chose Never.
This contradicts full Nash and proves the finite-support impossibility.

If a point of (8) with β=0 had L=0, (5) would be a finite-support actual
full Nash profile, which was just excluded. Consequently (10) implies

    λ>0,           z_j>0 for all j.                      (11)

In particular every date t<N has positive joint reach in the prescribed
profile: pivot survival is at least λ and nonpivot survival at least z_j.
All nonpivot conditional hazards are strictly less than one. These facts
are proved BEFORE the next backward induction is used.

## 5. Exact auxiliary payoff representation and derived symmetry

The plan-dependent subsidy in (8) must not simply be treated as a
continuation payoff. Here that replacement is justified by an equality
of the ENTIRE finite normal-form payoff function, as follows.

Fix m. For every pure tuple of the three nonpivot plans, integrate the
independent pivot clock (5). Player j's compensation term Δ_j z_j in
mixed laws is λD. It is the expectation of the pure-plan payoff

    λ·1_(all three nonpivot plans are Never).             (12)

This identity holds for every unilateral replacement, because D_j
omits the responding player's own law. If at least one nonpivot plan
is finite, (12) is zero and the game certainly ends before N unless
the pivot already ended it. If all three plans are Never, the original
post-deadline finite pivot arm contributes exactly −λ to each nonpivot;
(12) cancels it. The original contribution from the pivot's head is
unchanged, and its Never arm contributes zero.

Thus the subsidized expected payoff, for EVERY pure or mixed tuple,
equals the payoff in this actual finite auxiliary chance game:

- the independent chance clock has head probabilities x_t for t<N and
  no head arrival with probability λ+ν;
- early absorption has the original coalition rewards;
- if no early absorption occurs, the terminal payoff to all three
  nonpivots after the finite menu is zero.

This is equality after integrating the chance clock. It is not a claim
that an unconditional planned-Never subsidy is pathwise paid only at a
surviving terminal history. The special cancellation (12), and β=0,
are what make the auxiliary finite game legitimate.

The nonpivot laws in (8) are exact Nash in that finite chance game.
By (11) all its rows are positively reached. Changing a player's
conditional suffix while retaining its earlier law changes its payoff
by the positive joint reach times the conditional payoff change.
Therefore each conditional suffix is Nash in this auxiliary game.

At date t write h_t for the chance clock's conditional head probability
and q_j,t for the nonpivot hazards. Suppose the next conditional payoff
vector is zero, as is true at the final cut. We have h_t<1 and q_j,t<1.
The current values are

    Q_j=0,
    C_j=−h_t+(1−h_t)(2q_pred(j),t−q_succ(j),t).          (13)

Put k=h_t/(1−h_t)≥0 and suppress t. Nash requires

    2q_pred(j)−q_succ(j) ≥ k        if q_j=0,
    2q_pred(j)−q_succ(j) = k        if q_j>0.             (14)

If q_1=0 and k>0, the first inequality gives q_3>0. The equality for
player 3 gives q_2=k/2>0, and the equality for player 2 gives −q_3=k,
a contradiction. If q_1=0 and k=0, any q_3>0 forces q_2=0; player 2's
inequality would then give −q_3≥0. Hence q_3=0 and then q_2=0.
The same argument applies after a cyclic rotation.

If all q_j are positive, the three equalities in (14) have the unique
solution q_1=q_2=q_3=k: the cyclic coefficient matrix is invertible
with determinant 7. Thus, in every case, all three hazards agree and
all three row payoffs are zero. Backward induction proves at every t

    q_1,t=q_2,t=q_3,t=:q_t∈[0,1),
    h_t=q_t/(1+q_t),
    conditional auxiliary payoff = (0,0,0).             (15)

In particular all three ENTIRE nonpivot laws are identical. This is a
consequence for EVERY zero-bonus fixed point, not an invariant-subspace
restriction chosen by a logit or symmetry-preserving algorithm.

## 6. A uniform full-value bound from the actual laws

Define the surviving masses before date t by

    s_t=∏_(u<t)(1−q_u),     s=s_N>0,     D=s³,
    w_t=∏_(u<t)(1−h_u)=∏_(u<t)(1+q_u)^(−1),
    w=w_N=λ+ν.

Since 1/(1+q)≥1−q for q∈[0,1), we have w_t≥s_t, including w≥s.
The pivot's head atom satisfies

    x_t=w_t q_t/(1+q_t)
        ≥s_t q_t/2=(s_t−s_(t+1))/2.                     (16)

For a pure pivot quit at t<N the prescribed payoff is 2−s_t³; a pure
late quit gives 2−D and pure Never gives 2−2D. Hence B_0=2−D.
Put

    I=Σ_(t<N) x_t(s_t³−D) ≥0.

This is the probability that a pivot head arrival intercepts finite
nonpivot activity at that date or later. Direct substitution in (6)
gives the exact formulas

    U_0=2−I−(1+ν)D,
    d_0=I+νD.                                          (17)

By (10), I+νD≤λD. Therefore I≤L and λ≥ν. Together with w≥s this yields

    λ≥w/2≥s/2.                                         (18)

Since u↦u³−D is increasing and nonnegative on [s,1], the upper-endpoint
Riemann sum and (16) imply

    I ≥ (1/2)Σ_(t<N)(s_t−s_(t+1))(s_t³−D)
      ≥ (1/2)∫_s^1 (u³−D)du
      = 1/8−D/2+3s⁴/8.                                (19)

This finite-sum inequality also permits repeated endpoints q_t=0;
no diffuseness or bound on the size of a simultaneous atom is assumed.

If s≤1/2, then D≤1/8, so (19) gives L≥I≥1/16.
If s≥1/2, then (10) and (18) give L=λs³≥s⁴/2≥1/32.
This proves (1) for every finite deadline and every fixed point.

## 7. Positive bonuses give arbitrarily small global repair values

Here is the full comparison branch, including global inner optimality.
For K≥1 put N=3K, a=2^(−K), J=a³, and prescribe pivot Never with

    p_j(3k+j−1)=2^(−k−1),       0≤k<K,
    p_j(Never)=a,              j=1,2,3.

Take β_2=a² and β_1=β_3=0. The pivot point is λ=α=0, ν=1, so all
compensations Δ_j vanish. Against these laws and pivot Never, exact
pure response values are

    f_1(3k)=f_1(3k+1)=0,     f_1(3k+2)=−4^(−k)/2;
    f_2(3k)=1−4^(−k),       f_2(3k+1)=f_2(3k+2)=1;
    f_3(3k)=f_3(3k+2)=0,     f_3(3k+1)=−4^(−k)/2.

Never and all finite responses after the menu have values
(0,1−a²,0). These formulas follow by accumulating opponent absorption
strictly before the tested date; a response that itself quits receives
zero on its own quitting coalition. Consequently every prescribed
nonpivot finite action is an auxiliary best reply, and the Never bonus
ties player 2's Never value with its cap 1. Other players' Never values
already tie their caps 0. The original full values are

    U=(2−2J,0,1−J,0),
    B=(2−J,0,1,0),
    d=(J,0,J,0).                                        (20)

It remains essential to prove GLOBAL pivot optimality, not just the
nonpivot equations. Hold these three laws fixed and let g_2,1 be
player 2's original gain from pure time 1. For EVERY pivot law,

    d_0+g_2,1 ≥ 2J.                                    (21)

Both gains are affine in the pivot law. For pure pivot time 0 they
equal 1−J and 0, whose sum is at least 2J since J≤1/8. For
1≤t<N, the pivot debt is 2^(−t)−J≥J. Player 2's time-1 test pays
one, and inserting the pivot cannot increase its prescribed payoff
relative to pivot Never: pointwise the pivot either joins player 2
and still pays zero, or pays −1, the minimum possible original reward
on that outcome. Thus g_2,1≥J. For t≥N the pivot debt is zero and
g_2,1=2J, since adding the pivot only changes prescribed payoff on the
joint nonpivot Never event. At pivot Never both gains are J.

Integration proves (21) for arbitrary unbounded stopping laws. The
same affine inequality holds on the closed repair domain, because
these gains are independent of α. Since full E is at least each gain,
(21) bounds EVERY pivot repair below by J. Equality is attained in
(20). The displayed point is therefore a genuine fixed point of (8),
not a comparison law with unverified inner optimality. This proves (2).

Given any η,ε>0 and any prescribed minimum deadline N_0, choose K large
enough that 4^(−K)≤η, 8^(−K)<ε, and 3K≥N_0. This gives the stronger
arbitrarily-large-menu version of the positive part of (3).

## 8. Consequence for continuation and exact boundary tests

Set η_K=4^(−K). The source in Section 7 has L_K=8^(−K) and bonuses
at most η_K. Every zero-extra-bonus endpoint, at every larger finite
menu and even on any different component, has value at least 1/32.
Since L_K+ω(η_K)→0 for any ω(η)→0, principle (C) is false.

The examples and proof explicitly cover the following boundaries.

- Zero first atom with positive late mass: (5) preserves the entire
  original full payoff/cap data on this table because b_j=0. Such a
  boundary cannot bypass (1).
- Zero joint nonpivot Never mass or zero late pivot mass: by (10) this
  would give L=0 and an actual finite-support exact equilibrium, already
  ruled out. They are not removed by a generic interior assumption.
- Sure finite atoms: the finite-support zero-value exclusion handles
  reached sure rows before induction; positive fixed points have
  strictly positive residual masses and so cannot have such rows.
- Arbitrarily large simultaneous atoms: (14) treats all hazards below
  one, and (19) is a finite monotone sum, not a small-hazard limit.
- Extra zero dates, arbitrary finite calendars, and all optimizer
  branches: the argument never fixes a support pattern or a deadline
  bound. Zero dates are permitted by q_t=0.
- Positive bonus ceilings: these are NOT excluded. The asymmetric
  branch (20) lies in the original correspondence and has value tending
  to zero while its bonus tends to zero.

No endpoint statement at a fixed N conflicts with compactness: the
positive comparison has N=3K→∞. Equation (3) concerns precisely the
failure of a uniform-in-menu exchange between setting the bonus to
zero and taking an infimum over all menus.

## 9. Narrow correspondence and the remaining mathematical question

The route selected from `docs/TOOLKIT.md` is exact one-player behavioral
repair and the remaining finite nonpivot-law source. The declarations
inspected here and in the defining compensated-source proof are:

- `exists_objective_minimizer_eq_behavioral_infimum` and
  `isGLB_pivotLaw_exploitability_of_objective_minimizer` in
  `UniformEquilibrium/Quitting/Terminal/PivotRepairBehavioralInfimum.lean`;
- `HasQuittingSmallPivotRepairValue` and
  `exists_pivotRepairMass_objective_le_finiteMenu_exploitability` in
  `UniformEquilibrium/Quitting/Terminal/PivotRepairSmallValueSource.lean`;
- the finite objective and boundary endpoint definitions in
  `PivotRepairFiniteLP.lean` and `PivotRepairFiniteLPBoundary.lean`, as
  recorded in the [compensated-source proof](CODEX_RENY__LATE_CAP_COMPENSATED_NEVER_SELECTOR.md).

These sources identify the ORIGINAL inner optimization; they do not
assert that its nonpivot laws can be selected from this particular
compensated fixed-point class with small value. No Lean build was run
for the present note and no new result here is claimed Lean-checked.

The table and its finite approximate witnesses are already in the
[canonical separation note](CODEX_RENY__CANONICAL_EXACT_FINITE_MENU_SEPARATION.md).
The planned-Never positive selector was produced in HILBERT's
[private-bonus note](CODEX_HILBERT__VANISHING_PRIVATE_NEVER_BONUS_SELECTOR.md);
the stronger global pivot certificate used in Section 7 was established
in the [coupled-LP note](CODEX_RENY__PIVOT_LP_AND_FINITE_NONPIVOT_BEST_REPLY_COUPLING.md)
and reproduced in Section 5.2 of the compensated-source proof.

The earlier [symmetry-selector obstruction](CODEX_RENY__SYMMETRY_PRESERVING_LOGIT_SELECTOR_OBSTRUCTION.md)
bounds the full debt of prescribed identical nonpivot laws. It does not
force symmetry for all points of a correspondence allowing arbitrary
nonpivot laws. The new step here is the exact zero-continuation
representation and its reached-row induction, deriving that symmetry
for EVERY zero-extra-bonus compensated fixed point at EVERY menu.
The direct bound (19) makes this proof independent of the earlier
symmetry bound or any stationary-screen assertion.

The prior [fixed-menu tail-matching obstruction](CODEX_HILBERT__COMPENSATED_FIXED_POINT_TAIL_MATCHING_OBSTRUCTION.md)
classifies the N=1 global selected source and defeats a fixed-pivot
splice. It does not give (1) over all enlarged menus. The
[expressiveness test](CODEX_HILBERT__COMPENSATED_SELECTOR_EXPRESSIVENESS_TEST.md)
shows exact-zero completeness at each fixed N; it does not supply a
uniform approximate-to-exact selection bound as N grows. Finally the
[menu-unfolding note](CODEX_RENY__COMPENSATED_SELECTOR_MENU_UNFOLDING.md)
explains why compensation can telescope into EXTRA bonus without
improving the unchanged original value. The present result rules out
recovering a uniformly cheap zero-bonus endpoint even by unrestricted
reselection and menu growth on this fixed table.

This is not a new UE existence class, a positive-gap game, or a failure
of all regularized selectors. It only rejects the additional exactness
restriction β=0 and the uniform value orientation (C). The actual
positive-bonus question remains, using the general compensation
Δ_j=D_j[b_jα−a_jλ]₊ with a_j=r_j({0}), b_j=r_j({0,j}):

    For every canonical table and every η,ε>0, are there N≥1,
    β∈[0,η]³ and a fixed point of the general compensated rule
    (specializing to (8) on the displayed table) with L<ε?

The new result gives a reason not to try to prove that question by
first setting β identically zero. The requested independent check is
the pure-plan cancellation (12), the conditional-suffix agency, and
the all-menu lower bound, not another audit of the old good branch.
