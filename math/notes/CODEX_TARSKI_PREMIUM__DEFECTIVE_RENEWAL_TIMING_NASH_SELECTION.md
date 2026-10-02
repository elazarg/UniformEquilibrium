# Defective-renewal timing Nash: source and global selection question

Identity: CODEX_TARSKI_PREMIUM.

Status: active ordinary-mathematics research, not Lean-checked. The actual
finite-game Nash source exists; its full-response formula and exact
law-preserving refinements are proved below. Two difficult-for-earlier-methods
regressions have exact successful outputs. A uniform slow-pivot absorption
bound is valid, but its one-phase selection recipe fails at every Nash
output along an explicit parameter path. No arbitrary-table selection,
global decrease, or uniform-equilibrium theorem is proved. This is a new
question after the
[mandatory-proper quota format was retired](CODEX_TARSKI_PREMIUM__PERIODIC_QUOTA_NASH_AND_PROPER_CLOCK_FORMAT_BOUNDARY.md),
not an unannounced weakening of that program.

## 1. Actual source and exact selection question

Let I={0,1,2,3}, let r be an arbitrary real quitting reward table with
own singletons (1,0,0,0), and let |r_i(S)|≤M. Never and preabsorption pay
zero. All randomization is independent and private. A complete unilateral
behavioral replacement is allowed; it induces a law on ℕ together with
Never. Let U_i, B_i and E=max_i(B_i−U_i) be actual terminal payoffs, full
caps and exploitability.

Fix N≥1 and a vector c∈[0,1)^4. Player i has N+1 actions. The action ∞ is
literal permanent Never. Phase action t, 0≤t<N, is the proper law

    g_it(kN+t)=(1−c_i)c_i^k,  k≥0.

For mixed action weights a_it and z_i with Σ_t a_it+z_i=1, the actual law is

    μ_i(kN+t)=(1−c_i)c_i^k a_it,    μ_i(Never)=z_i.        (1)

Thus z_i is genuine Never mass, while c_i is conditional cycle survival
WITHIN the finite component. Parameters c are fixed by the external
selector; they are NOT actions of this finite game. All four phase/Never
weights are chosen jointly by its Nash conditions. Expected terminal
rewards define a finite normal-form game, so its mixed Nash set Q(N,c) is
nonempty and compact. Every output is an actual independent behavioral
profile; no public correlation or fictitious boundary payoff occurs.

The proposed producer question is

    for every canonical r and ε>0, do there exist N≥1, c∈[0,1)^4,
    and a∈Q(N,c) such that E(μ(a,c))<ε?                  (P)

Equivalently, does the infimum A(r) over ALL these exact finite-game Nash
outputs vanish? There is no asserted attainment as N varies or c approaches
one. A weaker completeness question assumes ordinary terminal approximate
equilibria already exist and asks whether this forces A(r)=0.

For fixed N,c, write a_r(N,c)=min_(a∈Q(N,c)) E(μ(a,c)). This minimum IS
attained: varying the finite weights changes actual marginal laws
continuously in total variation, and bounded-payoff coupling controls every
response uniformly, so E is continuous on the compact Nash set. This fixed
parameter minimum must not be identified with the global infimum A(r).

The raw FAMILY, without its Nash restriction, passes the expressiveness
test literally: c=0 represents every finite-menu law. It also contains
every periodic law: choose c_i equal to its one-period own survival, take
z_i=0 when c_i<1, and use the corresponding normalized phase masses;
a player whose periodic law is Never is represented by z_i=1 with any
allowed c_i. This does not prove expressiveness of the NASH OUTPUTS.

## 2. Exact full-response formula

Fix a profile (1), a player i and its opponents J=I\{i}. Define

    f_jt=(1−c_j)a_jt,
    b_jt=Σ_(u≥t) a_ju+c_jΣ_(u<t) a_ju.

Then, without conditioning away any reach,

    Pr(T_j=kN+t)=c_j^k f_jt,
    Pr(T_j≥kN+t)=z_j+c_j^k b_jt,
    Pr(T_j>kN+t)=z_j+c_j^k(b_jt−f_jt).

For a formal vector x=(x_j)_(j∈J), expand the two finite polynomials

    G_it(x)=Σ_(∅≠S⊆J) r_i(S)
               ·∏_(j∈S)(x_j f_jt)
               ·∏_(j∈J\S)[z_j+x_j(b_jt−f_jt)],

    Q_it(x)=Σ_(S⊆J) r_i(S∪{i})
               ·∏_(j∈S)(x_j f_jt)
               ·∏_(j∈J\S)[z_j+x_j(b_jt−f_jt)].

Write their squarefree coefficients as γ_itA and q_itA. The first has
zero constant coefficient; the second has constant s_iD_i, where
s_i=r_i({i}) and D_i=∏_(j∈J)z_j. For nonempty A⊆J put

    c_A=∏_(j∈A)c_j<1,    H_iA=Σ_(u<N) γ_iuA,
    W_i=Σ_(∅≠A⊆J) H_iA/(1−c_A),
    C_itA=q_itA+Σ_(u<t)γ_iuA−H_iA/(1−c_A).

Here G_it((c_j^k)_j) is the unconditional contribution of opponent
absorption at that date while i Continues, and Q_it is the contribution
when it Quits there. Summing contributions at all earlier dates gives

    F_i(kN+t)=W_i+s_iD_i+Σ_(∅≠A⊆J) C_itA c_A^k.         (2)

W_i is the literal Never payoff. All ratios have positive denominators;
zero rates are allowed with 0^0=1. Formula (2) has at most eight
exponential terms including its constant, with no assumed distinctness
of the bases. It also retains the finite-time limiting endpoint
W_i+s_iD_i, which need not equal Never.

The phase-action payoff follows by averaging its OWN geometric law:

    V_it=W_i+s_iD_i+
         Σ_(∅≠A⊆J) C_itA (1−c_i)/(1−c_i c_A).          (3)

Its denominator is again positive. Exact menu Nash means precisely

    U_i=max(W_i,max_t V_it),
    a_it>0 ⇒ V_it=U_i,    z_i>0 ⇒ W_i=U_i.              (4)

In contrast the ORIGINAL complete cap is

    B_i=max(W_i, sup_(k≥0,t<N) F_i(kN+t)).              (5)

Every behavioral response is an average of these pure finite-date and
Never values, proving (5) without a bounded-controller restriction.
Equation (4) does not replace the supremum in (5) by the phase averages.
Signed rewards, ties, zero weights, and all-opponent-Never profiles are
covered. In the latter case W_i=0 and F_i(kN+t)=s_i.

These formulas alone are a verifier. Their role here is to specify the
unresolved source selection, not to create a separate certificate language.
An exact rational arithmetic check compared (2) to direct first-event sums
and (3) to an independent mixture over pure geometric-phase/Never type
tuples. It passed 768 comparisons on twelve rational canonical tables with
periods 1,2,3 and rates chosen from 0,1/3,1/2,2/3 (seed 6014). This is a
bounded formula regression, not evidence for the unproved selection (P).

## 3. Two actual output regressions

For the canonical proper-clock obstruction table in the linked quota note,
choose player 0's phase-zero action and all other players Never. This is
exact full Nash for EVERY N and rate vector c: the pivot obtains its solo
reward 1 against three Never opponents, and each other player gets its
coordinate maximum 2. Thus it is also menu Nash. The proof does not replace
any Never clock by a positive-rate clock.

The second table is the existing VANISH benchmark. Its pivot gets 1 when
participating and 2 otherwise. For each j∈{1,2,3}, its payoff is zero when
participating, −1 when absent but 0 participates, and otherwise
2·1_(pred(j)∈S)−1_(succ(j)∈S), with predecessor and successor cyclically
ordered among 1,2,3. Never is zero. The own singleton vector is canonical.

Set N=3, let player 0 use Never, and let each nonpivot j use phase j−1
with c_j=1/2. Its actual law is

    Pr(T_j=3k+j−1)=2^(−k−1),    Pr(T_j=Never)=0.

The pivot's Never value and complete cap are both 2. The complete response
maxima for players 1,2,3 are respectively (0,1,0), and their prescribed
finite atoms all attain those respective values. For player 2 the
cumulative opponent payoff before cycle k is 1−4^(−k), after player 1's
row it is 1, and after player 3's row it is 1−4^(−k−1). For players 1,3
the cumulative value at every prescribed row is zero and all intervening
values are nonpositive. This checks every date and the Never limits.
Thus the actual profile is full exact Nash and consequently belongs to
Q(3,c), regardless of c_0. This is the known cyclic equilibrium, not a new
existence theorem. Unlike the original finite-menu Nash sets of VANISH,
this changed producer has an exact zero-debt output.

## 4. Same-law period refinement

For any K≥1 the very same actual law (1) has a representation with period
N'=KN, rates c'_i=c_i^K and weights

    a'_(i,kN+t)=a_it (1−c_i)c_i^k/(1−c_i^K),  0≤k<K,
    z'_i=z_i.                                           (6)

Their finite total mass is Σ_t a_it. Multiplying the new geometric
cycle factors verifies every actual finite atom, and Never is unchanged.
Thus ALL actual payoffs and full caps are unchanged by (6). The new Nash
conditions are stronger, however: old phase action t is a convex mixture
of the K new phase actions with weights
(1−c_i)c_i^k/(1−c_i^K). Therefore refined-menu Nash implies old-menu
Nash for this identical law, but the converse need not hold.

If an old-menu Nash profile has full exploitability e>0, some finite pure
date t has gain greater than 3e/4: Never cannot witness positive gain,
and a finite date approximates any nonattained finite-date supremum.
Choose K so that t<KN and 2M c_i^K<e/4 for that deviator i. Its new phase-t
action uses pure t with probability 1−c_i^K and otherwise a later time.
Its payoff differs from F_i(t) by at most 2M c_i^K, so its refined-menu
gain exceeds e/2. Consequently the SAME law fails refined Nash.

This is a source-retaining exposure statement, not a descent theorem.
Ordinary expanding pure-time menus also eventually expose each fixed
profitable deadline. Re-solving the larger finite game changes all four
laws and need not retain their old payoff or cap ordering. Neither (6)
nor finite-game Nash existence implies that the newly selected equilibrium
has smaller full E. In particular a putative positive global infimum A(r)
is not contradicted merely because each of its particular witnesses fails
some refined game's Nash equations.

## 5. A tested parameter recipe: slow pivot is not enough

There is a genuine uniform consequence of choosing the pivot's renewal
much slower than its opponents'. Put

    e(c,z)=2M Σ_(j>0) (1−z_j)(1−c_0)/(1−c_0c_j).

For EVERY phase t and EVERY profile of the fixed-parameter game,

    |V_0t−(W_0+D_0)|≤e(c,z).                             (7)

Indeed compare the pivot's geometric stopping time to a hypothetical
response that waits past every finite opponent clock, and quits only
when all opponents choose Never. The latter is used only as an outcome
comparison, with expected reward W_0+D_0; it is not claimed to be a legal
strategy. The two outcome rewards can differ only if the pivot stops no
later than some finite opponent. For opponent j that event has probability
at most

    (1−z_j) E[c_j^(pivot cycle)]
      =(1−z_j)(1−c_0)/(1−c_0c_j).

A union bound and the coordinate reward bound prove (7). At any menu Nash
with z_0>0, (4) gives V_0t≤W_0, and hence D_0≤e(c,z). If z_0=0 the actual
all-Never probability is already zero. Thus EVERY output satisfies

    Pr(all Never)=z_0D_0≤e(c,z)
      ≤6M(1−c_0)/(1−max_(j>0)c_j).                      (8)

This is an actual-source absorption statement. It is not a full-regret
statement, as the following exhaustive parameter-path test shows.

Use VANISH from Section 3. Fix N=1, c_1=c_2=c_3=0 and
25/26≤c=c_0<1, and write h=1−c. The unique menu Nash output is

    pivot: its proper geometric action, Never mass zero;
    each nonpivot: Quit0 with probability
        m=(3−sqrt(9−4/c))/2, otherwise permanent Never.  (9)

Here is the complete uniqueness argument, including mixed pivot choices.
Let x be the pivot's probability of choosing its geometric action and q_j
the nonpivots' Quit0 probabilities. A nonpivot's Quit0 payoff is zero. Its
Never payoff, with a=pred(j), b=succ(j), is exactly

    W_j=(1−xh)(2q_a−q_b)−xh−xc(1−q_a)(1−q_b).          (10)

If q_j=1, its successor has W≥1−2xh>0 and must have hazard zero.
The predecessor then has W=−1 and must have hazard one. This makes j's
own W=2−3xh>0, a contradiction. So all q_j<1 and all W_j≥0.
If x>0 and q_j=0, (10) makes its successor's W strictly negative,
another contradiction. Thus x>0 forces all three q_j into (0,1).

If x=0, the equations are the ordinary cyclic zero-continuation root.
Taking a maximal positive q_j would force its successor zero, then its
predecessor zero, which gives that predecessor a negative W. Hence all
q_j=0. But the pivot's geometric action then pays 1 instead of Never's
zero, excluding x=0. Therefore all W_j=0 and all q_j∈(0,1).

Put β=xh/(1−xh) and γ=xc/(1−xh)≤1. These equations say that successive
opponent coordinates satisfy

    b=T(a)=[(2+γ)a−γ−β]/[1−γ+γa].

The denominator is positive at the interior coordinates, and
T'(a)=(2−γ+γβ)/(1−γ+γa)^2>0. A strictly increasing map has no nonconstant
three-cycle, so all q_j=m. Write z=1−m. Then m=γz²+β.

If 0<x<1, pivot indifference would require

    (1+h)z³=h.

Our h≤1/26 gives z≤1/3 and m≥2/3. But γ≤1 and β≤h/c≤1/25 imply
m≤1/9+1/25<2/3, impossible. Thus x=1. The nonpivot equation now gives
3m−m²=1/c, whose unique interior solution is (9). It lies between
(3−sqrt(5))/2 and 2/5, so z≥3/5. The pivot's geometric-versus-Never
gain is (1+h)z³−h>0, checking its remaining best-reply inequality.
This proves uniqueness among ALL mixed equilibria of this fixed game.

The ORIGINAL response calculation is equally explicit. Each nonpivot
has prescribed payoff and Never payoff zero, pure Quit0 value zero, and

    F_j(k)=cz² c^(k−1),    k≥1.

Therefore its full debt is cz². The pivot has prescribed payoff
1+c(1−z³), cap 2−z³ and debt h(1−z³). Hence

    E=cz²≥9/26,
    E → (3−sqrt(5))/2>0 as c→1.                         (11)

At c=25/26, m=2/5 and E=9/26, all exact. The actual all-Never probability
is identically zero throughout this path. Thus the slow-pivot recipe fails
for EVERY one-phase Nash output, not merely an inconvenient selected one.
This is not an obstruction to global A(r): Section 3 already gives A=0
for this same table at period three. No radius or constant optimization,
new equilibrium class, or export is proposed for this method regression.

## 6. Consumer and precise remaining question

For a supplied output with small E, after K cycles its i-th finite tail
mass is (1−z_i)c_i^K. Censoring these finite tails to Never changes full
exploitability by at most

    4M Σ_i (1−z_i)c_i^K.

This follows by coupling prescribed clocks and, separately, opponents
uniformly over every unilateral replacement. Thus (P), if established,
would produce actual finite-law approximate equilibria and enter the
existing all-errors terminal consumer. No supplied feasible payoff is the
target of this selection question.

The next mathematical question is global, not another cap identity:
assuming A(r)>0, can Nash feasibility together with ALL parameter and
phase choices orient an exposed refinement into an equilibrium with value
below A(r), or can an explicit solved table have A(r)>0? A positive
restricted-menu minimum, a bad chosen Nash equilibrium, or a Nash-breaking
profitable deviation at the old law would not answer it.

A first precise source-level comparison now under test is

    a_r(KN,(c_i^K)_i) ≤ a_r(N,c) for every K≥1.           (12)

It compares minima over the WHOLE two Nash sets, not an arbitrary Nash
continuation or the identical law in (6). It is neither proved nor used
above. A bounded exact support scan of 160 two-player canonical rational
tables, at N=1, rates (1/2,2/3), and their K=2 refinements found no violation
among the enumerated equal-cardinality support equilibria. Degenerate
equilibrium continua and the four-player case were not certified by that
scan; this is only an initial test, not positive evidence at theorem level.
If (12) fails, the genuinely global question remains whether freely
reselecting rates at the larger period repairs the comparison. Even (12)
alone, without strict/quantitative progress, would not imply A(r)=0.

Exact menu Nash is a chosen source, not the semantic target. If useful,
the source can be relaxed to approximate menu Nash, but two errors must
then be controlled: with H_i=max(W_i,max_t V_it),

    B_i−U_i=(H_i−U_i)+(B_i−H_i).

Both terms are nonnegative. A vanishing first term does not compensate for
a fixed positive second term; the unique outputs of Section 5 already have
the first term zero and the second bounded away from zero. No approximate
source producer controlling both terms has yet been derived.

## 7. Finite heads repair closure, not global progress

Adjoin an arbitrary finite head of length H≥0: each player's menu contains
the H pure head dates, the N geometric phase laws shifted by H, and
permanent Never. Its law has arbitrary head atoms and a tail of form (1).
Fixed H,N,c still give a finite normal-form game and a compact exact Nash
set. Unlike headless renewal laws, this enlarged family is literally
closed under every finite timing Nash block at its ACTUAL payoff U.

For completeness let such a block have length L, playerwise Continue
probabilities y_i, deleted Continue a_i=∏_(j≠i)y_j, finite-date payoff
maximum Q_i, and Continue payoff C_i=H_i+a_i U_i. Here H_i denotes only
the block's absorbing contribution, not the head length. Put
n_i=max(Q_i,C_i), the block Nash payoff. Follow the block and, conditional
on private Continue, the old head/renewal law. This belongs to the same
family with head length H+L, unchanged N,c, and Never mass y_i z_i.

Every shifted old menu action has value at most C_i and every supported
one attains C_i; supported block dates attain n_i. Block Nash therefore
proves exact Nash in the new FULL head/phase/Never menu. Actual complete
caps and debts satisfy

    B'_i=max(Q_i,C_i+a_i d_i),    U'_i=n_i,
    d'_i=[a_i d_i−(n_i−C_i)]₊≤a_i d_i.                (13)

This is precisely the zero-bonus case of NOETHER's
[whole timing-block comparison](CODEX_NOETHER_SUPPORT__WHOLE_TIMING_BLOCK_BONUS_COMPETITION.md),
not a new prefix mechanism. The headless family was not closed, but this
repair alone does not supply strict progress.

Indeed let b be the infimum of E over ALL exact Nash outputs in this
head-enlarged family. At a source with E≥b, EVERY such Nash block obeys

    b≤max_i a_i d_i≤E·max_i a_i.                      (14)

Thus near-minimality controls only the MINIMUM deleted absorption among
possible debt owners: 1−max_i a_i≤(E−b)/E. It does not single out the
pivot. If a positive b is attained, a block activating at least two players
has every a_i<1 and contradicts (14). A block activating only k can retain
b only if d_k=b and n_k=C_k. Since k's positive finite block actions all
pay its singleton, block Nash then gives U_k=s_k. Consequently every block
at such a minimizer is all Continue or activates only a maximal debtor
whose actual payoff equals its own singleton. No limit-root persistence
or lower-semicontinuity is inferred when b is not attained.

This reproduces the inactive-continuation difficulty in the
[all-root bonus-source analysis](CODEX_NOETHER_SUPPORT__ALL_ROOT_RESTRICTION_AT_GLOBAL_BONUS_MINIMA.md).
It is in one respect weaker: exact renewal-menu Nash does not bound the
three nonpivots' full debts by a vanishing bonus ceiling. Section 5 has
three positive nonpivot full-response gaps despite zero menu error. Thus
there is no automatic analogue of NOETHER's one-pivot error localization.
No strict global comparison, new API, or prefix-closed selector theorem
is proposed on the strength of this composition alone.

## 8. Narrow source correspondence

The pure-time semantic interface was inspected in
`sSup_range_quittingTerminalPayoff_update_eq_pureTime`
(`UniformEquilibrium/Quitting/Cycles/BehaviorPureTimeExtremality.lean`).
The displayed proof includes the mixture argument needed for full responses.
Finite positive-rate periodic windows are already evaluated by
`sSup_range_quittingTerminalPayoff_update_eq_periodicWindow`
(`UniformEquilibrium/Quitting/Cycles/PeriodicWindowEvaluation.lean`);
nonzero permanent Never mass generally destroys literal periodic hazards,
so that declaration is not simply applied to (1).

[Geometric pivot compression](../formalized/GEOMETRIC_PIVOT_TAIL_COMPRESSION_AND_EXACT_REPAIR_LP.md)
preserves fixed finite opponent laws and optimizes one complete pivot law;
it does not select Nash weights for four renewal clocks. The
[time-prior logit producer](CODEX_FRECHET_CYCLE__TIME_PRIOR_LOGIT_GEOMETRIC_PRODUCER.md)
uses a different entropy-regularized finite-action game and a proved
table-specific comparison set. Neither implies (P).

The successful cyclic source and its exact comparisons were checked against
[the VANISH bonus note](CODEX_HILBERT__VANISHING_PRIVATE_NEVER_BONUS_SELECTOR.md)
and [the coupled pivot/nonpivot note](CODEX_RENY__PIVOT_LP_AND_FINITE_NONPIVOT_BEST_REPLY_COUPLING.md).
This packet invokes their known infinite periodic profile, not the bonus
selector or any claimed universal equilibrium-selection convergence.
