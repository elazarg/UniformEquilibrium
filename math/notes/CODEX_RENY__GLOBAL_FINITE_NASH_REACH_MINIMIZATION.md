# Global finite-menu Nash reach minimization

Author: `CODEX_RENY`.

## Current status

Ordinary mathematics, not Lean-checked. Sections 2–5 have an independent
PASS review by HILBERT in
[`CODEX_RENY__GLOBAL_FINITE_NASH_REACH_MINIMIZATION__BY_CODEX_HILBERT.md`](../feedback/CODEX_RENY__GLOBAL_FINITE_NASH_REACH_MINIMIZATION__BY_CODEX_HILBERT.md).
The later source-comparison tests are author calculations, not covered by
that review. The exact
finite-menu prefix formula is an adapter of existing root Bellman/cap
identities. Its global-selection consequence is the proposed new statement:
if minimum early reach over ALL finite e-Nash laws stays bounded away from
zero as deadlines grow, every asymptotically minimizing payoff/debt limit
(u,d) has only the all-Continue exact root Nash at u, all four finite debts
dᵢ=e, and a reciprocal singleton-surplus obstruction displayed in Section 5.

The one-sure-owner endpoint is treated by first softening its new root and
only then changing its old tail law. Changing the old tail alone at a sure
root would fail. No uniform equilibrium, low-reach producer, or table-wide
contradiction is claimed. The solved cyclic delayed branch is an early test,
not a candidate positive-gap game. Section 9 tests one genuinely nonlocal
operation, whole-block private retry. It strictly reduces survival but can
violate EVERY fixed error budget even at true global reach minimizers; that
arbitrary-table implication is stopped, with its exact scope retained. The
negative-membership minimizer has no positive singleton, while the positive
cyclic test is not globally minimizing: neither refutes the intended
positive-singleton GLOBAL-minimizer target. Sections 10–11 audit the
two-parameter error budget and isolate an unproved trade that WOULD yield
early absorption. They do not assert that this trade exists.

## 1. Actual finite optimization problem and bounded source audit

Fix a finite player set I, |I|=m≥2, rewards |rᵢ(S)|≤M with M>0, zero Never
payoff, and independent privately randomized stopping laws. Put sᵢ=rᵢ({i}).
For deadline N≥1 use the SAME menu A_N={0,…,N−1,Never} for prescribed laws
and all unilateral tests. For a product law p write

    Uᵢ(p) = prescribed terminal payoff,
    Fᵢ,a(p) = pure-a payoff against p₋ᵢ,
    Cᵢ(p) = max[a∈A_N] Fᵢ,a(p),
    dᵢ(p) = Cᵢ(p)−Uᵢ(p) ≥ 0.

The finite e-Nash set is F_N(e)={p: dᵢ(p)≤e for every i}, with e>0 fixed.
Its definition includes all N+1 pure deviations; affine dependence on the
deviator's law makes these equivalent to all mixed finite-menu deviations.
It is compact and nonempty by finite mixed Nash existence. For fixed H≥1
and N≥H put

    a_N(e,H) = min[p∈F_N(e)] R_p(N−H),
    a = liminf[N→∞] a_N(e,H).

Assume a>0, choose Nₙ→∞ and actual minimizers pⁿ with
R_{pⁿ}(Nₙ−H)→a, and pass to a subsequence with

    U(pⁿ)→u,       d(pⁿ)→d∈[0,e]^I.

The finite timing encoding and exact payoff/test adapters were inspected in
`UniformEquilibrium/Diagnostics/Quitting/FiniteDeadlineTimingGame.lean`:
`quittingFiniteDeadlineTimingGame`,
`quittingTerminalPayoff_finiteDeadlineTimingProfile_eq_mixedEU`, and
`quittingFiniteDeadlineTimingProfile_update_pureTime_eq_mixedEU`.
The chronological finite Bellman adapter is `timingMixedPayoff_bellman` in
`UniformEquilibrium/Diagnostics/Quitting/FiniteDeadlineTimingRecursion.lean`.
The full-debt analogue of Section 2 is
`quittingTerminalDeviationDebt_rootThenContinuation_eq` in
`UniformEquilibrium/Quitting/Root/TerminalDebtPrefix.lean`; its complete
deviation cap is NOT silently identified with the finite Cᵢ above.

Nearby no-gos were checked narrowly. The HAHN notes
`CODEX_HAHN__FINITE_CLOCK_EXPLOITABILITY_KKT_BOUNDARY_OR_CROSS_AMPLIFICATION.md`
and `CODEX_HAHN__FINITE_CLOCK_KKT_FIXED_FACE_OR_FULL_TIMING_BUBBLE.md`
minimize FULL exploitability, including the first omitted date, and obtain
active-response multipliers/cross-amplification. They do not minimize reach
over a finite-menu e-Nash sublevel set. The exact finite-Nash noncompleteness
and deadline-enlargement failure are retained in the predecessor
[`CODEX_RENY__APPROXIMATE_FINITE_TIMING_NASH_AND_REACH.md`](CODEX_RENY__APPROXIMATE_FINITE_TIMING_NASH_AND_REACH.md).
The quantile-clock hierarchy and its productive-certificate corollary
approximate the unknown full-debt infimum; they do not make it zero or
produce low-reach finite e-Nash laws. No new general KKT theorem or sparse
clock approximation is being proposed here.

## 2. Exact fresh-date formula on the enlarged menu

Prepend one independent product root q∈[0,1]^I, and shift every old finite
date by one. Conditional on own Continue at the new date, each player uses
its old law. The new law is on A_{N+1}; Never stays Never. This is an actual
construction, not a claim that the old source was Nash on an enlarged menu.

Let Qᵢ(q) be new-date Quit payoff, let Cᵢ(q;u) be new-date Continue payoff
followed by old prescribed payoff uᵢ, and put

    P₋ᵢ(q)=∏[j≠i](1−qⱼ),       A(q)=∏ⱼ(1−qⱼ),
    Vᵢ(q;u)=qᵢQᵢ(q)+(1−qᵢ)Cᵢ(q;u).

The maximum gain over all lifted OLD actions is exactly

    Lᵢ(q;u,d)=P₋ᵢ(q)dᵢ+qᵢ(Cᵢ(q;u)−Qᵢ(q)).        (2.1)

The gain at the newly available date zero is exactly

    Zᵢ(q;u)=(1−qᵢ)(Qᵢ(q)−Cᵢ(q;u)).                (2.2)

Thus the new finite-menu regret is max(Lᵢ,Zᵢ), with no hidden date tests.
Indeed, the absorbing payoff contribution while i Continues is the same for
every lifted old action and the old prescribed law; its difference is just
P₋ᵢ times the old payoff difference. Subtracting the new prescribed root
mixture supplies the second term of (2.1). All mixed tests are averages of
these pure tests. The reached objective obeys the exact identity

    R_new(N+1−H)=A(q)R_old(N−H).                       (2.3)

Every expression in (2.1)–(2.2) is continuous in the fixed-dimensional data
(q,u,d), even though N varies. This is the useful compact source interface.

As a preliminary consequence, a positive-reach minimizer on a fixed menu
N>H cannot have all dᵢ<e. Replacing one marginal by a sufficiently small
mixture with Quit0 reduces R(N−H) multiplicatively and changes every finite
regret by at most 4M times the mixture mass. This strict-slack observation
alone is not the main result below.

## 3. Positive exact root Nash would improve the asymptotic minimum

### Proposition

Under the Section 1 hypotheses, every exact root Nash q at continuation u is
all Continue. In particular uᵢ≥sᵢ for every i, and the all-Continue root is
the unique exact root Nash at u.

### At least two active root coordinates

Suppose q has at least two positive coordinates. Then P₋ᵢ(q)<1 for EVERY
player i. Exact root Nash gives Zᵢ(q;u)≤0 and
qᵢ(Cᵢ(q;u)−Qᵢ(q))≤0. Consequently

    Lᵢ(q;u,d)≤P₋ᵢ(q)e<e,       Zᵢ(q;u)<e.

By continuity, the SAME root q prepended to pⁿ is finite e-Nash on its
enlarged menu for all sufficiently large n. Equation (2.3) gives limiting
reach A(q)a<a at deadlines Nₙ+1→∞, contradicting the definition of a.

### Exactly one active root coordinate

Let k be the only active player, with q_k=t>0. Here the owner's opponent
survival is one, so it has no contraction slack. Exact root Nash says

    s_k≥u_k;       if t<1, then s_k=u_k.               (3.1)

If t=1 and s_k>u_k, (2.1) gives L_k=d_k+u_k−s_k<e.
Every outsider has P₋ᵢ=0 and every new-date regret is ≤0, so the previous
continuity argument applies directly.

It remains to handle s_k=u_k. First arrange a FIXED active probability
0<t'<1. If t<1, retain t'=t. If t=1, choose t'<1 sufficiently close to one
that every outsider's new-date regret remains strictly below e; this is
possible because at t=1 all such regrets are ≤0 and e>0. The softened root
need not be exact Nash. It has the exact owner equality Q_k=C_k=s_k at u,
and every outsider's old-menu gain equals (1−t')dᵢ<e.

If d_k<e, all required inequalities now have strict slack. Otherwise d_k=e.
For each n choose a best reply b_kⁿ in the OLD menu against pⁿ₋k. Change
only k's OLD law to

    p̃_kⁿ=(1−λₙ)p_kⁿ+λₙδ_{b_kⁿ},

where, for sufficiently large n with d_kⁿ>0, choose

    λₙ = [d_kⁿ+t'(u_kⁿ−s_k)−e]₊ / ((1−t')d_kⁿ).     (3.2)

Then λₙ→0, so eventually λₙ≤1. This raises k's old prescribed payoff by
λₙd_kⁿ while leaving its old finite cap fixed. After prepending the softened
root, k's maximum old-menu gain is EXACTLY

    d_kⁿ+t'(u_kⁿ−s_k)−(1−t')λₙd_kⁿ ≤ e.             (3.3)

Its new-date gain tends to zero and is eventually below e. Every outsider's
old finite regret changes by at most 4Mλₙ, uniformly in Nₙ; its new-date
gain changes continuously with the old prescribed payoff, by at most 2Mλₙ.
The fixed outsider contraction and new-date slack therefore survive. The
constructed laws are finite e-Nash on A_{Nₙ+1}.

Changing the old owner law can change the old reached objective by at most
λₙ, hence its reach still tends to a. The final prefix multiplies it by
1−t'<1, again contradicting the asymptotic minimum.

This proves that no positive exact root exists at u. Finite binary-game Nash
existence then forces all Continue to be Nash, which is precisely u≥s.
The argument at t=1 does NOT assert that changing an unused old tail alone
can repair a sure root. Softening the root is essential before (3.2).

## 4. Every finite-menu error budget is saturated

### Proposition

Under the same hypotheses, dᵢ=e for every player i.

If d_k<e, prepend a root with only k active, with probability t>0 small.
Because u≥s, at t=0 every new-date gain is sᵢ−uᵢ≤0<e. For k,
L_k=d_k+t(u_k−s_k)<e when t is sufficiently small. Every outsider has
Lᵢ=(1−t)dᵢ<e. All new-date gains remain <e by continuity. The inequalities
are strict at the limiting data, hence this same root works for all late
pⁿ and contradicts a>0 through (2.3).

Thus no asymptotically minimizing coordinate can retain an unused error
budget. This is strictly stronger than the fixed-menu observation that at
least one constraint is tight. It uses GLOBAL selection over growing menus,
the ability to prepend a date, and the root-uniqueness proposition.

## 5. A reciprocal singleton-surplus obstruction

Put bᵢ=uᵢ−sᵢ≥0. A root qᵢ=t hᵢ with hᵢ≥0 and ∑hᵢ=1 has, at t=0,

    d/dt Lᵢ = hᵢ(bᵢ+e)−e.                           (5.1)

Indeed P₋ᵢ=1−t∑[j≠i]hⱼ+O(t²), while Cᵢ−Qᵢ=bᵢ+O(t).
Every new-date gain is initially −bᵢ≤0, separated from the allowed e.

If ∑ᵢ e/(e+bᵢ)>1, choose

    hᵢ = (e/(e+bᵢ)) / ∑ⱼ(e/(e+bⱼ)).

Then every derivative in (5.1) is strictly negative. A sufficiently small
fixed t gives Lᵢ<e and Zᵢ<e for every i, and hence again supplies a uniform
reach reduction for the approximating source sequence. Contradiction.
Therefore every such minimizing limit satisfies

    ∑ᵢ e/(e+uᵢ−sᵢ) ≤ 1.                            (5.2)

For m≥2 every uᵢ>sᵢ follows: a zero surplus would contribute one by itself
and the remaining terms are strictly positive. Cauchy–Schwarz also gives

    ∑ᵢ(uᵢ−sᵢ) ≥ m(m−1)e,

in particular at least 12e for Fin4. These are constraints on the ACTUAL
payoff limit of globally minimizing finite near-equilibria. They are not
assertions that the singleton-surplus vector is executable as a continuation,
and they are not a table-wide contradiction for an arbitrary reward table.

## 6. Solved cyclic test and the remaining obstruction

Use the all-normal Fin4 completion in Section 14 of the predecessor note.
The delayed exact finite Nash has payoff (3/2,3/2,3/2,7/4), singleton
values all one, and finite debts all zero. For 0<e≤1/8 prepend a root with
only active player 0 quitting, with probability t=2e. The old-menu gains
are e for player 0 and zero for everyone else. The new-date gains are

    player 0: −(1−t)/2,
    player 1: −1/2−t/2,
    player 2: −1/2+3t/2,
    player 3: −3/4−t/4.

All are below e. The actual new finite e-Nash source reaches its old
window with probability 1−2e<1. Thus the delayed exact branch is not a
global positive-error reach minimizer; the relaxed optimization really
escapes that earlier selector obstruction. This is an exact test of the
construction, not a proof of arbitrary repeated descent.

After every budget becomes tight, (5.2) can block all strict first-order
fresh-date directions. It does not imply that every nonlocal clock
reallocation is blocked. Conversely, a feasible direction at a non-minimizer
does not prove that minimizing reach tends to zero. The current result is a
new proposed source restriction from GLOBAL minimization, not a replacement
for the robust final-window equivalence and not a uniform-equilibrium
consumer.

## 7. Same-source comparisons in error and window length

The following comparison does not silently select different laws. Given
p∈F_N(e), N>H, mix one player's law with the pure date-zero law with weight
x∈(0,1). A single coupling changes every prescribed or pure-test payoff
by at most 2Mx. Thus every finite debt increases by at most 4Mx, whereas
the objective changes EXACTLY to (1−x)R_p(N−H). Consequently, for
0<δ<4M,

    a_N(e+δ,H) ≤ (1−δ/(4M)) a_N(e,H).

Taking the liminf preserves this inequality. At the same e, increasing H
increases every profile's reach objective, so

    a_N(e,H+1) ≥ a_N(e,H),
    liminf_N a_N(e,H+1) ≥ liminf_N a_N(e,H).

The first comparison genuinely improves survival but spends δ of the
finite-menu error budget. It does not improve reach at the original e.
Iterating it with a bounded total error expenditure gives only a positive
product lower scale when all increments stay uniformly below 4M. Neither
comparison by itself forces a positive-reach threshold to disappear.

## 8. Coherent solved-table test across every small e and every H

This test checks whether merely following the restrictions of Sections 3–5
as e or H varies can close the argument. It uses ONE explicit family, not
an unsupported comparison of independently reselected limits.

Use the all-normal cyclic Fin4 completion from Section 6. For 0<e≤1/8 put

    q=(1+√(1+8e))/4,       q(2q−1)=e,
    B=2(1−(1−q)³),        y=e/(B−1).

At the final date all three active players Quit independently with
probability q; player 3 Quits with probability y. Otherwise each chooses
Never. Insert any number of all-Continue dates before that final date.
Since q≥1/2, B≥7/4 and 0<y≤1/6.

For each active player, the final-date Quit and Never payoffs are 1+q and
3q. Hence

    uᵢ=4q−2q²,       cᵢ=3q,       dᵢ=q(2q−1)=e.

Player 3's Quit and Never payoffs are 1 and B, so

    u₃=B−e,          c₃=B,        d₃=e.

All earlier finite dates give own singleton payoff 1, below every displayed
uᵢ. Thus this is a finite e-Nash law for EVERY deadline N≥1, with the same
payoffs and all four debts exactly e. For every N≥H its entry reach into
the final H dates is one. Moreover,

    uᵢ≥3/2 (i<3),       u₃≥13/8,
    ∑ᵢ e/(e+uᵢ−1) ≤ 6e+(4/3)e ≤ 11/12 < 1.

The exact root game at u has only all Continue. First player 3 strictly
prefers Continue: its payoff is a convex combination of 2 and u₃>1,
whereas Quit pays 1. It is therefore absent from any root equilibrium.
For an active player i, writing a=q_pred(i), b=q_succ(i), its root gap is

    Qᵢ−Cᵢ = 1−2a−uᵢ(1−a)(1−b).

There cannot be a sure active quitter: a sure i makes its successor
strictly Continue, then makes its predecessor strictly Quit, which makes
i strictly Continue. If one active hazard is zero, the predecessor's gap
is ≤−1/2−a/2<0, and the remaining player's gap is ≤−1/2; all are zero.
If all three hazards are positive and less than one, all three gaps vanish.
Using uᵢ≥3/2 gives

    b ≥ (1+a)/(3(1−a)) > a,

which is impossible around a cycle. This proves uniqueness of all Continue.

Therefore the entire limiting restriction package—strict singleton
surpluses, unique all-Continue root, all debts equal e, and strict reciprocal
inequality—is compatible with one coherent family for all 0<e≤1/8 and all
H in a game with an exact periodic terminal Nash equilibrium. These laws
are NOT global reach minimizers: the equilibrium and finite approximation
give liminf_N a_N(e,H)=0. This is not a counterexample to Sections 2–5.
It shows that threshold variation of their conclusions alone cannot
replace another substantive use of global selection. No further local
necessary-condition regression is intended here.

## 9. One nonlocal operation: whole-block private retry

This is a bounded construction test, not another necessary-condition
refinement. Given one actual N-date product law p, let each player use it
through the first N dates. If play remains alive, everyone independently
resamples its own ENTIRE law for another N-date block. Repeat K times and
then use Never. These are legal private randomizations with fixed calendar
boundaries; no common random seed or observation of a deviation is used.

Write aᵢ=pᵢ(Never), A=∏ᵢaᵢ, Dᵢ=∏[j≠i]aⱼ, uᵢ=Uᵢ(p),
νᵢ=Fᵢ,Never(p), and Fᵢ=max[a<N]Fᵢ,a(p). Let vᵢ(K) and cᵢ(K) be the
prescribed payoff and the cap on the ACTUAL enlarged KN-date finite menu.
Then, exactly,

    vᵢ(K)=uᵢ∑[0≤k<K]Aᵏ,
    cᵢ(0)=0,
    cᵢ(K+1)=max{Fᵢ, νᵢ+Dᵢcᵢ(K)}.                 (9.1)

Every first-block finite stopping date has its old payoff, because i has
already Quit before a second block could matter. Every later stopping date,
including Never, Continues through the whole first block and gives the old
opponent-absorption ledger νᵢ plus Dᵢ times its relative payoff in the
remaining blocks. This enumerates all new finite-menu deviations, proving
the cap recursion. Prescribed recursion instead uses JOINT survival A.

For fixed H≤N, the entry reach of the K-copy profile into its final H dates
is A^(K−1)R_p(N−H). Thus whenever 0<A<1 the operation strictly reduces the
objective. Its feasibility condition, however, is the NEW inequality

    cᵢ(K)−uᵢ∑[0≤k<K]Aᵏ ≤ e     for every i,        (9.2)

not the source condition cᵢ(1)−uᵢ≤e.

### Solved all-normal cyclic test

For the delayed exact one-date branch in Section 6, active coordinates have

    uᵢ=Fᵢ=νᵢ=3/2,       A=1/8,       Dᵢ=1/4.

Two copies therefore have

    vᵢ(2)=27/16,         cᵢ(2)=15/8,
    cᵢ(2)−vᵢ(2)=3/16.

So whole-block retry is NOT an e-Nash-preserving source operation for any
0<e≤1/8, even though its source is exact finite Nash and its reach contracts.
This is an exact finite-menu defect, not merely an untested late deviation.
The source is not globally minimal; the next test retains global minimality.

### Failure at exact global reach minimizers of an arbitrary table

Use the m-player reward rᵢ(S)=−1 if i∈S and zero otherwise, and take
0<e<1/m. Never gives every player its cap zero against every opponent law,
so dᵢ is exactly its probability of belonging to the first absorbing
coalition. Every finite e-Nash law therefore has total absorption at most
∑ᵢdᵢ≤me and entry reach at least 1−me at every date.

For N≥H+m this bound is attained before the final H dates. At its own
successive date i∈{0,…,m−1}, player i Quits with independent probability

    hᵢ=e/(1−ie),

and otherwise chooses Never. The probability i is the first quitter is
exactly e, since the preceding joint survival telescopes to 1−ie. All
absorption is by singletons, and

    Uᵢ=−e,       dᵢ=e,       A=1−me,
    a_N(e,H)=A.

These are genuine GLOBAL minimizers for every sufficiently long deadline,
not stationary examples, local KKT points, or independently supplied
continuations. Retrying the whole profile twice gives joint Never mass A²
and payoff −e(1+A) to every player. The finite caps stay zero, so EVERY
new finite debt equals e(1+A)>e. Thus (9.2) fails simultaneously everywhere.

The table has no positive own singleton and is solved by all Never. It does
not refute the positive-singleton producer target. It does refute the
proposed generic implication

    globally minimum positive reach in F_N(e)
      ⇒ repeated independently resampled blocks remain in F_KN(e).

The signed-reward obstruction is concrete and table-wide. Consequently no
arbitrary-table retry lemma is claimed. For positive-singleton tables one
would need a new incentive argument or a new selection in the enlarged
finite game; writing “reselect a Nash law” does not establish that the new
selection retains the retry profile's smaller reach. That exact missing
comparison is where this operation stops.

### Bounded mechanism distinction

The genuinely different mechanism identified in
`ideas/NONLOCALITY_TECHNIQUE_CATALOGUE.md`, NL-18, and
`ideas/CURRENT_NONLOCALITY_RECOMMENDATIONS.md`, R11, is degree/index or a
continuation branch of the ACTUAL finite product-game equilibrium
correspondence. It would have to force a branch into the low-reach region,
not merely produce another root at the limiting payoff vector. No such
branch theorem is proved here. The existing
`QuittingFiniteDeadlineCompatibleNashFamily` and
`exists_uniformEquilibriumPayoff_of_arbitrarilySmallAdjacentNashTV` in
`UniformEquilibrium/Diagnostics/Quitting/FiniteDeadlineProjectiveCompatibility.lean`
already consume compatible or sufficiently close adjacent exact selections;
they explicitly do not produce them from deadlinewise finite Nash existence.
The exact finite-Nash incompleteness no-go also forbids adopting that exact
selection architecture universally. Any new topological construction must
retain positive finite-menu error and actual enlarged-menu constraints.

## 10. Actual error–reach comparison and its diagonalization limit

Fix H≥1. Section 7 gives a comparison on the ENTIRE finite feasible set,
proved by changing a real product law, not a formal derivative:

    a_N(e+δ,H) ≤ (1−δ/(4M))a_N(e,H)                 (10.1)

for every N>H, e≥0, and 0<δ<4M. The case e=0 uses an attained finite Nash
law just as the positive-error case uses an attained finite e-Nash law.
At each step the output is feasible on the SAME complete finite menu; one
may legitimately replace it by that menu's new global minimizer because
the latter has no larger objective.

Consider ANY finite iteration using this estimate, with initial allowance
e₀≥0, increments δ₀,…,δ_(K−1)>0, and final allowance

    e_K=e₀+∑[k<K]δ_k ≤ E < 4M.

The multiplier certified by (10.1) satisfies

    ∏[k<K](1−δ_k/(4M))
        ≥ 1−∑[k<K]δ_k/(4M)
        ≥ 1−E/(4M).                                (10.2)

This is the elementary product/union inequality. It is a LOWER bound on
the multiplier in the certified UPPER estimate, not a lower bound on the
actual minimum reach. Thus no impossibility of better reselected laws is
claimed. Rather, this proven comparison alone supplies a contraction factor
tending to ONE as the final error E tends to zero. It cannot establish a
vanishing-reach diagonal from seeds bounded only by a_N≤1.

The conclusion holds regardless of how tiny the initial positive allowance
is or how many stages are used. Monotonicity of the feasible sets lets one
discard unused allowances, but does not refund past regret increments. A
change of deadline would require another actual-menu comparison: no such
comparison is supplied merely by inserting dates or selecting a different
minimizer. Taking the cofinal liminf in (10.1) preserves it but does not
improve the multiplier calculation.

## 11. One precise productive trade, and the missing extra efficiency

The following is an UNPROVED construction claim, recorded only to make the
two-parameter test falsifiable. Its conclusion is genuinely sufficient for
early absorption, not merely another necessary condition.

Fix the reward table and H≥1. Suppose there are κ>0, c>0, and e*>0 such
that, for EVERY 0<e≤e*, EVERY N>H, and every actual minimizer p of
a_N(e,H), one can construct some deadline N′>N and an actual product law
p′ on its complete menu satisfying

    p′∈F_N′(e+κe²),
    R_p′(N′−H) ≤ (1−ce)a_N(e,H).                    (11.1)

We may shrink e* so ce*<1. The constants may depend on the fixed table
and H, but not on e, N, or the source minimizer. A weaker statement that
selects one minimizer on each old menu is also enough, provided the same
construction can be reapplied after each legitimate new-menu selection.
The quantifier N′>N ensures cofinal deadlines and is part of the claim,
not a false padding assertion.

### Exact iteration if (11.1) were proved

Choose E>0 with 2E≤e* and κE≤1, and L>0. Start at any deadline above the
desired lower bound N₀ and H with a global minimizer at allowance

    e₀=E exp(−L).

Such a minimizer exists; exact finite Nash existence ensures the feasible
set is nonempty even at this very small allowance. Define recursively

    e_(k+1)=e_k+κe_k².

At each stage apply (11.1), then reselect a global minimizer on the ACTUAL
new deadline N_(k+1). Its reach is no larger than that of the constructed
p′, so this reselection is a proved comparison, not source identification.
Stop at the first K with e_K≥E. It exists in finitely many steps because
each increment is at least κe₀². The last overshoot obeys

    E≤e_K≤E+κE²≤2E.

Moreover,

    log(e_K/e₀)
      =∑[k<K]log(1+κe_k)
      ≤κ∑[k<K]e_k,

so ∑[k<K]e_k≥L/κ. All successive reach comparisons therefore give

    a_NK(e_K,H)
      ≤∏[k<K](1−ce_k)
      ≤exp(−c∑[k<K]e_k)
      ≤exp(−cL/κ).                                 (11.2)

Letting E tend to zero and L tend to infinity produces actual finite-menu
laws with both error and final-window reach tending to zero, at deadlines
above any prescribed N₀. More explicitly, for requested ε,ρ>0 first choose
2E≤ε and then L with exp(−cL/κ)<ρ. Hence (11.1) would solve the
early-absorption producer at the chosen H. If it held for every H, the
reviewed completion would yield terminal approximate Nash profiles at every
accuracy and then a uniform payoff by the existing terminal compiler.

### Why the available operation does not prove (11.1)

With δ=κe², the actual mixture comparison (10.1) gives only
1−κe²/(4M), whereas (11.1) needs 1−ce. In the iteration above,

    ∑[k<K]e_k²=(e_K−e₀)/κ≤2E/κ,

so the existing quadratic-size reach improvements have bounded total size
tending to zero. The missing factor 1/e in reach gained per unit added
regret is exactly what the desired nonlocal selection must supply.

Whole-block retry does not supply it either: the positive-singleton cyclic
test in Section 9 starts at exact finite Nash but has a fixed finite regret
3/16 after only two copies. This refutes retry as an operation on arbitrary
sources at error e+κe² for all sufficiently small e. It does NOT refute
(11.1), whose source is a genuine global minimizer. The negative-membership
global-minimizer test refutes a sign-unrestricted version of the trade but
does not settle its positive-singleton version.

No component-crossing theorem, homotopy argument, or new finite-game
selection establishes (11.1) here. Merely asserting that a new minimizer
can be selected with the desired smaller reach would assume the missing
producer. Conversely, once arbitrarily low-reach sources already exist,
one could ignore the input and select such a source; that is not an
independent proof mechanism. The contribution of this section is the exact
budget and quantifier audit, not existence of the productive trade.

## Next concrete check

The independent Sections 2–5 check is complete. The generic retry operation
is stopped at (9.2), with the positive-singleton global-minimizer target
still open. The actual error-spending comparison cannot diagonalize by
(10.2). A new substantive step would have to PRODUCE (11.1), a comparable
efficient nonlocal trade, or a direct actual enlarged-menu selection with
vanishing error and reach. No such producer, component crossing, or new
export gate is claimed. The external completion has a PASS review in
`feedback/COMPLETION__BY_CODEX_RENY.md`; it removes a consumer obstacle,
not this selection obstacle.
