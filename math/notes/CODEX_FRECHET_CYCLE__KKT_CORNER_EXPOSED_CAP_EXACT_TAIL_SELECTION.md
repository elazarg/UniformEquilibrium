# KKT corner surgery: exact selection of the one exposed cap

Identity: CODEX_FRECHET_CYCLE.

## Status and precise question

Ordinary mathematics, not Lean-checked. The bounded calculation below solves
the actual one-opponent tail optimization left exposed by a singleton screen.
With nonnegative owner singleton, one extra finite date beyond the two fixed
opponents' calendars suffices, even when the admissible replacement initially
ranges over every infinite behavioral strategy. It preserves the complete
earlier response envelope. It does not prove that the optimized cap has the
sign needed for global regret descent, and does not add a UE class. It does
exclude improvement of a genuine fixed-calendar global minimum by this
entire infinite-tail family unless both pair endpoints are strictly below
the owner's singleton; the two-active-player inward-premium witness is in
the excluded subcase.

The question came from the global finite-clock KKT source, not a local
stationary point. For four independent laws on
A_K = {0,...,K−1,Never}, let

    E(P) = max_i (B_i(P)−U_i(P)),       η_K = min_P E(P),

where B includes every finite response date, the after-menu response K, and
Never. In the internal KKT arm, distinct players j,i have active responses
r,t, and i has a prescribed support time s with

    V_i,t(μ[j←r]) − V_i,s(μ[j←r]) ≥ η_K/3.

Consider the chronological case s < r < t, with s finite. At the actual
corner C = μ[i←s,j←r], can freely choosing j's whole law after s orient i's
full cap and improve the GLOBAL objective? The exact optimization is now
explicit. The remaining KKT comparison is stated in Section 5 rather than
assumed. No hypothetical positive global minimum is replaced by an example
from a solved table.

## 1. Exact scope of the screen

More generally, fix an actual profile with i surely quitting at date s and
j never quitting through s. Keep the other two independent stopping laws
fixed. Replace j's complete law by any independent law supported strictly
after s, including Never.

Every prescribed terminal payoff is unchanged. Every unrestricted cap B_k
with k ≠ i is unchanged: the fixed player i still stops the game by s after
any unilateral replacement by k. This includes the changed player j's cap.
Only B_i can change. This is a singleton screen, not a pure-pair screen.

Write T_R for the earliest of the two unchanged opponents' stopping times,
and S_R for the coalition of those opponents stopping at T_R. Let

    A_u = V_i,u(C_-i),                         0 ≤ u ≤ s,
    A = max_{0≤u≤s} A_u,
    H = E[r_i(S_R) 1_{T_R≤s}],
    ρ = Pr(T_R>s).

The definition of H excludes Never. All these numbers are independent of
j's replacement. In particular U_i(C)=A_s and A≥U_i(C). If ρ>0, condition
the two unchanged laws separately on surviving strictly past s. Independence
is retained. For a chosen j tail ν let b(ν) be i's unrestricted cap in the
conditional game starting at s+1 against ν and those two conditional laws.
Then the complete response identity is

    B_i(C[j←ν]) = max{A, H+ρ b(ν)}.                         (1)

If ρ=0, the corresponding expression is max{A,H}, with no conditional game
needed. Equation (1) retains every earlier response branch, not just s or t.
It follows by splitting each later pure response according to T_R≤s and
T_R>s. A behavioral response only averages pure finite responses and Never.

## 2. An unlimited two-clock tail has an attained short optimum

The following scalar calculation is the boundary condition, not an assumption
about strategic incentives of j. Suppose only i,j remain capable of quitting,
and set

    σ = r_i({i}) ≥ 0,    a = r_i({j}),    b = r_i({i,j}).

Over ALL independent behavioral stopping laws ν of j, starting at the current
date, the minimum unrestricted cap of i is

    v_* = min{σ, max{a,b}}.                                 (2)

The minimum is attained by j=Never if max{a,b}≥σ, and by j quitting surely
at the current date otherwise. This includes equality and σ=0.

Here is an elementary unrestricted lower bound. If b≥σ, quitting at the
current date gives at least σ. If a≥σ, the payoffs of i's finite dates tending
to infinity converge to

    a Pr_ν(j finite) + σ Pr_ν(j Never) ≥ σ.

Thus max{a,b}≥σ forces cap at least σ. If a,b<σ, quitting at the current date
gives at least b, and the same late-finite limit gives at least a. Hence the
cap is at least max{a,b}. These bounds match the two displayed laws. The
late-finite test cannot be replaced by Never, whose payoff is
a Pr_ν(j finite), possibly smaller when σ>0.

Equivalently, for F(v)=min_{0≤y≤1} max{(1−y)σ+yb,(1−y)v+ya},

    F(σ)=v_*,                F(v_*)=v_*.                     (3)

Thus the finite-calendar dynamic problem stabilizes after one additional
punisher date once the two unchanged opponents have no finite dates left.

## 3. Backward recursion and an actual minimizing law

Suppose the two fixed opponents' finite dates are all less than K. Take
K>s, increasing it if necessary. They may have positive Never mass. At date
K only i,j can still quit, so use (2) and its actual minimizing action there.
At each date u=K−1,...,s+1, condition the unchanged opponents on survival to
u. If a conditioning event has zero probability, choose its later hazards
arbitrarily; an earlier zero continuation coefficient screens the choice.

Let p_u(S) be the independent product probability that exactly S among these
two opponents quit at u. Define

    q_0 = Σ_S p_u(S) r_i(S∪{i}),
    q_1 = Σ_S p_u(S) r_i(S∪{i,j}),
    h_0 = Σ_{S≠∅} p_u(S) r_i(S),
    h_1 = Σ_S p_u(S) r_i(S∪{j}),
    c   = p_u(∅).

Given the already optimized continuation value v_{u+1}, put

    v_u = min_{0≤y≤1}
          max{(1−y)q_0+yq_1,
              (1−y)(h_0+c v_{u+1})+y h_1}.                (4)

The minimizing y is j's actual hazard at u. It can be selected among 0, 1,
and the intersection of the two affine functions when that intersection is
in [0,1]. Thus rational rewards and fixed rational laws give rational values
and a finite rational replacement law.

For completeness, (4) optimizes over infinite tails, not merely the displayed
menu. Against any fixed choice of j's present hazard and future law, i's
unrestricted cap is the maximum of its Quit payoff and Continue payoff with
the future unrestricted cap substituted. The coefficient of that future cap
is (1−y)c≥0. By backwards induction, replacing the future law by its attained
minimum weakly lowers the current cap for every present y. Minimizing y then
gives (4), and the displayed hazard together with the already chosen actual
tail attains it. The initial induction step is the unrestricted theorem (2).

The selected law of j uses only dates s+1,...,K and Never. Its complete
response menu for i includes K+1 and Never: after adding the new date K,
quitting at K and waiting until K+1 are different tests, with payoffs b and
a on the pure terminal j row. This is exactly the boundary matrix in (3).

Consequently the optimum in the original corner is attained and equals

    B_i^opt = max{A, H+ρ v_{s+1}}.                          (5)

No correlated lottery is used. The two fixed opponents are unchanged, and
j's selected hazards are one ordinary independent stopping law. This is a
scalar adversarial optimization of i's cap; no best-response or Nash property
of the selected j law is asserted.

## 4. Exact boundary checks

A genuine mixture can be necessary before the final boundary. Take owner
i=0, free opponent j=1, player 2 surely quitting at date 1, and player 3
Never. Owner 0 quits at date 0, while j must survive date 0. Specify its
reward coordinate by

    r_0({0})=1, r_0({2})=3, r_0({0,1,2})=4,
    r_0(S)=0 on every other nonempty S.

Take all other reward coordinates zero. At date 1, matrix (4) has rows
(0,4) and (3,0). Its minimum is 12/7 at y=3/7. The earlier response at date
0 gives 1, so B_0^opt=12/7 and owner debt is 5/7. Either deterministic choice
at date 1 is worse. Taking j initially at date 2 gives cap 3. This checks
the actual cap reduction, while also showing that the optimized cap need not
equal the corner's prescribed payoff. The table has a zero-regret profile;
this is only a formula test, not a global-minimum/KKT counterexample.

Nonnegativity in the unlimited boundary theorem is substantive. With only
i,j active, take σ=−1, a=−2, b=−1/2. The Never boundary for i is zero. One
available j date gives value −4/5 at hazard 2/5. Two available dates give
value −16/17, with initial hazard 2/17 and terminal hazard 2/5. Therefore one
extra date need not stabilize the signed problem. This does not concern the
canonical nonnegative-singleton application of (2).

The two affine functions in (4), their endpoint/intersection minimizer, and
these rational values supply direct exact reproduction of the boundary
checks; no floating-point optimum is used in their proofs.

## 5. What the global KKT source does and does not imply

Put E_-i=max_{k≠i}(B_k(C)−U_k(C)). It is invariant under the whole surgery.
The optimized actual full exploitability is exactly

    E_opt = max{E_-i, A−U_i(C),
                       H+ρ v_{s+1}−U_i(C)}.               (6)

If C comes from the global minimizer on A_K, the optimized profile lies in
A_{K+1}; hence genuine global comparison supplies

    E_opt ≥ η_{K+1},                                       (7)

not automatically η_K. These are attained global minima on their displayed
finite calendars, not an attained all-behavior global minimum. Under a
hypothetical positive limit η_K↓m, the right-hand side is at least m.

There is a sharper complete comparison when

    max{r_i({j}), r_i({i,j})} ≥ σ.                          (8)

The boundary selector (2) then takes j=Never at and beyond K. Thus the
optimized j law actually lies on the ORIGINAL A_K, as do i=s and the two
fixed opponents. Global minimality on A_K gives E_opt≥η_K. Since it is the
minimum over ALL infinite j tails, every such tail replacement has
exploitability at least η_K. This is a theorem about genuine global finite
minimizers, independent of any local stationary-point reasoning. In this
subcase the entire unlimited tail surgery adds no better competitor to the
original calendar. It cannot beat m either.

Consequently a possible strict horizon-extension improvement by this
operation requires the strict double-low pair

    a=r_i({j})<σ,              b=r_i({i,j})<σ.              (9)

Then (2) chooses j surely at the one new date K. Whether that choice beats
η_K is EXACTLY the comparison of all three entries in (6) with η_K, not a
consequence of (9) alone. In particular, the KKT-selected paid difference gives
no upper bound on the invariant E_-i or A−U_i(C), and no upper bound below m
on the last term of (6). The free-tail choice is now solved rather than left
implicit, but these remaining inequalities have not been established or
refuted under the complete global-minimum hypotheses.

The double-low alternative also forces a third clock into the marked paid
interval. In the KKT notation, let g=V_i,t(μ[j←r])−V_i,s(μ[j←r])≥η_K/3,
where s<r<t, and δ=σ−a>0. Against the two fixed opponents put

    p=Pr(s≤T_R≤r),        q=Pr(T_R>r),        ρ_s=p+q.

The two i responses agree in payoff if T_R<s. If T_R>r, their difference
is exactly a−σ=−δ: the early response wins alone at s, and the late response
is passive at j's sure date r. On s≤T_R≤r their difference is at most 2M.
Therefore

    g ≤ 2M p−δ q,
    p ≥ (g+δρ_s)/(2M+δ) ≥ g/(2M).                         (10)

The last inequality also follows directly from g≤2Mp. One of the two fixed
opponents consequently has stopping mass at least g/(4M)≥η_K/(12M) in the
actual interval [s,r]. This is a literal marginal-clock mass bound, not a
prescribed atom bound at the original mixed profile and not a favorable debt
orientation. It identifies a clock that the fixed-two-opponent surgery is
not allowed to move.

The inward product-low violation supplies an actual root with no sure
quitter and positive own-singleton Quit premiums on its active support.
I inspected the declaration and its construction. It does not identify that
root with the fixed opponents' conditional hazards in (4), and does not bound
the passive entries h_0,h_1 or the earlier cap A. On a two-player active
support its own Quit premium is exactly q_j(b−σ)>0, so b>σ and (8) holds.
For either orientation, this witness therefore lies in the proved
NO-EXTENSION subcase, not the strict double-low option. Supports of size
three or four do not determine the sign of an individual pair endpoint.
No Nash-root or strategic-source conclusion is inferred from the witness.

The concrete remaining question is whether the FULL global KKT geometry
forces one chronological corner and orientation for which all three entries
in (6) are below the limiting minimum, or instead forces a useful joint move
of one of the two currently fixed opponents. The calculation does not make
this missing orientation a new supplied-object consumer or a solved branch.

## 6. Third-clock gate test against genuine finite-calendar minima

Changing another opponent only AFTER s cannot alter the invariant nonowner
terms in (6), even if every post-gate opponent law changes. I therefore tested
a stronger gate modification, not merely another tail optimization.

Take the literal H table from my
[global repair note](CODEX_FRECHET_CYCLE__GLOBAL_REPAIR_MINIMUM_CALENDAR_EXTENSION.md),
but replace r_1(S) by −1/2 whenever {1,2}⊆S and 0∉S. For self-contained data,
the unchanged rows are

    r_0(S)=1+1[2∈S] if 0∈S, and 3·1[2∈S] otherwise;
    r_1(S)=1[0∈S] if 1∈S, and 3·1[0∈S]−1 otherwise;
    r_2(S)=1[1∈S] if 2∈S, and 3·1[1∈S]−1 otherwise;
    r_3(S)=0 if 3∈S, and 1 otherwise,

followed by that single stated override. Never pays zero. The singleton
vector is (1,0,0,0), and the owner-punisher pair i=1,j=2 is strictly double
low: r_1({2})=−1 and r_1({1,2})=−1/2, both below σ=0.

Consider the ENTIRE actual family in which player 1 quits surely at date 0
and player 2 survives date 0. Allow arbitrary independent, possibly infinite
laws for all other coordinates, including arbitrary post-date-0 laws for
players 0 and 3. Thus the incident third clock 0 may change at the gate,
before its old absorption date, and in its whole future; this is larger than
the single gate-hazard test with retained conditional tails.

Write q=Pr(T_0=0), d=Pr(T_3=0), x=1−q. Prescribed absorption is sure at zero.
Directly from the table,

    U_0=U_1=q,     U_2=2,     U_3=1−d,
    B_0=1,        B_2=2,     B_3=1.

For player 1, use the complete response Quit1. When 0 quits at zero its
payoff is 2. If 0 continues and 3 quits, it is −1. If both continue, its
date-1 Quit payoff is at least −1/2 for every possible coalition. Hence

    B_1 ≥ 2q−(1−q)d−(1−q)(1−d)/2,
    d_1 ≥ 1−3x/2−xd/2.

Therefore every profile in this whole family has

    E ≥ max{x,d,1−3x/2−xd/2} ≥ c,
    c=(√33−5)/2.                                         (11)

For the last inequality, E≥x,d implies
E≥1−3E/2−E²/2; the nonnegative solution requires E≥c. Equality is attained:
player 0 puts mass 1−c at zero and c at Never; player 3 puts mass c at zero
and 1−c at Never; player 1 quits at zero; player 2 quits at one. The complete
caps are (1,1,2,1), the payoffs are (1−c,1−c,2,1−c), and E=c. To check the
only exposed cap, player 1's Quit0 gives 1−c, Quit1 gives 1 by the quadratic
identity c²+5c−2=0, and every later finite date or Never gives a weakly smaller
value because waiting past player 2's sure date gives −1 instead of −1/2.

This can be compared to ACTUAL GLOBAL finite-calendar minima, not just a
better unrelated local point. This modified table has η_K>0 at every finite
K. Indeed an exact finite-law Nash profile can have no reached sure quitter:
q_0=1 forces q_1=0, then q_2=1, then q_0=0; q_1=1 forces q_2=0 and then
q_0=1; q_2=1 forces q_0=0 and then q_1=1, since −1/2>−1. A sure player 3
would gain by Never if any other current hazard is positive; if all are zero,
player 0 gains by joining it. Each contradiction uses immediate absorption
and is independent of the off-path tail. At an exact Nash profile every
reached suffix is Nash by a literal suffix deviation. Thus every finite date
has positive joint continuation, and after the last supported finite date
the reached all-Never suffix admits player 0's gain-one Quit deviation.
Compact finite-calendar attainment then gives η_K>0.

On the other hand, the old H half-hazard solo cycle remains exact unrestricted
Nash: its prescribed outcomes are only singletons, so its payoffs are
unchanged; the modification only lowers player 1's possible deviation rewards.
Its three values remain (1,1,0,1), (1,0,1,1), (2,0,0,1). Truncating after
two cycles and then playing all Never gives the same finite laws as in the
old H calculation and does not raise any regret. Its proved bound gives

    0 < η_K ≤ 2·4^(−2)+8^(−2)=9/64 < c,       K≥6.         (12)

Thus EVERY gate competitor above loses to the genuine global finite-calendar
minimum for K≥6, despite optimizing the formerly fixed third clock and
allowing unlimited tails. The strict double-low option and one new punisher
date do not themselves control the nonowner regret created by making player
1 a sure early owner.

This is NOT a counterexample to the positive-limit KKT target. The table has
infimum over all behavior equal to zero, and I have not shown that its global
minimizers produce the specific KKT labels and s=0 used by this gate family.
The logical use of (11)–(12) is a complete test of the proposed joint gate
comparison, with genuine finite-global values distinguished from the
all-behavior infimum. It does not replace the missing implication from the
full KKT/global positive-limit data.

## Sources and overlap

Named declarations inspected in their files, without a Lean build:

- `exists_minimum_quittingControllerFiniteWordLoss`,
  `antitone_quittingControllerFiniteWordValue`, and
  `tendsto_quittingControllerFiniteWordValue`, in
  `UniformEquilibrium/Quitting/ControllerTester/FiniteWordValue.lean`.
- `quittingTerminalSemanticPair_literalRootStack_pureSet_screen`, in
  `UniformEquilibrium/Quitting/Paths/PureNonsingletonCommonPrefixScreening.lean`.
- `HasProductLowQuittingPremium` in
  `UniformEquilibrium/Quitting/Classification/ProductLowQuittingPremium.lean`,
  and `not_hasProductLowQuittingPremium_iff_exists_inwardViolation` in
  `UniformEquilibrium/Quitting/Classification/ProductLowQuittingPremiumInwardViolation.lean`.

The [global KKT two-law checkpoint](CODEX_NOETHER_SUPPORT__GLOBAL_KKT_TWO_LAW_COMPETITOR_CHECKPOINT.md)
retains the same full-envelope obstruction. The present computation uses its
whole-law corners but does not prove its requested global descent.
[Pure-clock deadline-rank descent](../formalized/PURE_FINITE_CLOCK_MINIMUM_DEADLINE_RANK_TO_PAID_PORT.md)
and [arbitrary-clock purification](../formalized/ARBITRARY_CLOCK_MINIMUM_PURIFICATION_TO_OFF_MINIMUM_PAID_PORT.md)
already lead to an off-minimum paid port; they do not orient (6). The
[pure-pair screening no-go](CODEX_ADVERSARY__PURE_PAIR_SCREENED_TWO_PORT_CAUSAL_TRANSPORT_NOGO.md)
screens every cap, unlike the singleton exposed coordinate here.

My [earlier global changed-tail punishment test](CODEX_FRECHET_CYCLE__REACHED_ENTRANCE_GLOBAL_TAIL_PUNISHMENT_TEST.md)
already minimizes the owner's cap when ALL opponent tails may change and
records the unresolved head contribution. Nothing here supersedes that
larger admissible optimization. The distinct limited calculation fixes two
actual calendars and minimizes over one opponent's entire law, with attained
finite selection and the exact nonnegative one-extra-date boundary.
[Finite-menu punishment completion](../exports/FINITE_MENU_PUNISHMENT_COMPLETION_AND_EARLY_ABSORPTION_CHARACTERIZATION.md)
already uses scalar backward punishment operators and is not re-proved here.
