# Independent review of the finite-menu low-reach completion

Reviewer: `CODEX_RENY`. Source: [`COMPLETION.md`](../archive/COMPLETION.md),
read in full. Verdict: **PASS as ordinary mathematics**, with the minor
expository clarification of finite-cap convergence below. No substantive
mathematical repair is needed. This is one independent review, not a full
export gate or a Lean-checked result. The source and exports were not edited.

The author explicitly claims only a completion from a SUPPLIED low-reach
finite-menu near-equilibrium. That scope is correct. No early-absorption
producer, equilibrium-selection theorem, or unrestricted UE conclusion from
arbitrary game data is supplied.

## 1. Exact theorem and probability mode checked

Let I be any nonempty finite player set, with arbitrary real rewards
rᵢ(S) for nonempty absorbing coalitions S, |rᵢ(S)|≤M, M≥0, and payoff
zero on Never. Strategies use independent private randomization. There is
one live public history at each date: everyone previously Continued.
Equivalently, each behavioral strategy on the live path is a stopping law
on ℕ∪{Never}; arbitrary unilateral behavioral deviations are allowed.

For H≥0, let mᵢ(H) be the infimum, over independent opponent laws on
{0,…,H−1,Never}, of i's best-response cap on that SAME finite menu.
Let Pᵢ be the infimum over all behavioral opponent profiles of i's
unrestricted terminal best-response cap, and set

    ω(H)=maxᵢ (Pᵢ−mᵢ(H))₊.

For any deadline N≥H, any finite-menu e-Nash product law p at its ACTUAL
deadline N, and any ρ with R_p(N−H)<ρ, every η>0 admits a behavioral
profile p̂ identical to p before t=N−H and satisfying

    E_r(p̂) ≤ e+2Mρ+max{2M√ρ, ω(H)+η}.                 (1)

Moreover mᵢ(H)→Pᵢ for every player, hence ω(H)→0. No positivity of own
singleton rewards, punishment normality, Fin4 restriction, full-Nash
assumption on p, or deviation-detection ability is used. The empty-player
case is vacuous if empty maxima are assigned value zero; otherwise the
displayed maxima simply call for the usual nonempty-player convention.

## 2. Finite punishment Bellman recursion

Fix i. For an independent opponent root y, let Q(y) be Quit-now payoff,
A(y) the unconditional absorbing contribution when i Continues, and
c(y) the probability all opponents Continue. Define

    Φ(x)=min_y max{Q(y), A(y)+c(y)x}.

The opponent root cube is compact and the displayed function is continuous,
so the minimum is attained for every real x. The exact recursion is

    mᵢ(0)=0,             mᵢ(H+1)=Φ(mᵢ(H)).            (2)

Indeed every opponent stopping law decomposes into its first Bernoulli root
and, conditional on own Continue, a remaining H-date stopping law. On the
all-opponents-Continue event those conditional laws are still independent.
The deviator either Quits now or Continues and makes its optimal remaining
finite-menu choice. For fixed y, minimization of the latter continuation
cap gives mᵢ(H); the coefficient c(y) is nonnegative and the same
continuation can be chosen independently of the root. When c(y)=0 the
continuation term is irrelevant, so no conditioning on a zero-probability
event is needed. Finite compactness also gives attainment in this argument.

This is centralized choice of a PRODUCT opponent profile, not correlated
opponent play. No minimax interchange with the deviator is invoked.

The map Φ is nondecreasing, 1-Lipschitz on ℝ, and maps [−M,M] into itself.
Its iterates from zero are monotone: increasing if Φ(0)≥0, decreasing if
Φ(0)≤0. Thus mᵢ(H) has a limit ℓᵢ∈[−M,M], and continuity gives
Φ(ℓᵢ)=ℓᵢ. This argument is valid for rewards of either sign; one must not
assert that the sequence is always increasing.

## 3. Identification of the limit and the delicate c=1 case

### The lower comparison ℓᵢ≤Pᵢ

Fix an infinite product opponent law p₋ᵢ. Replace every finite stopping
time at least H by Never, obtaining p₋ᵢᴴ on the H-date menu. For every
date a<H, the pure-a payoff is EXACTLY unchanged. The Never payoff differs
by at most

    2M ∑[j≠i] Pr_p(H≤Tⱼ<∞),

which tends to zero. Consequently its finite-menu cap is

    max{ max[a<H] Fᵢ,a(p), Fᵢ,Never(pᴴ) },

and converges to max{sup[a<∞] Fᵢ,a(p), Fᵢ,Never(p)}, the unrestricted cap.
This supplies the missing explicit justification behind the source's brief
convergence sentence. Mere pointwise convergence of arbitrary tests would
not generally suffice; here exact agreement of EVERY retained finite test,
the increasing finite maximum, and the late-finite-mass estimate do suffice.
Each finite cap is at least mᵢ(H), hence ℓᵢ≤Pᵢ after taking limits and then
the infimum over infinite opponent laws.

### The upper comparison Pᵢ≤ℓᵢ

For x>ℓᵢ, nonexpansiveness and Φ(ℓᵢ)=ℓᵢ give Φ(x)≤x. Choose a minimizing
root y. Then Q(y)≤x and A(y)+c(y)x≤x.

If c(y)<1, stationary repetition of this product row has unrestricted cap

    max{Q(y), A(y)/(1−c(y))} ≤ x.

To check this without a transversality assumption, Quit at date n has
payoff A(1−cⁿ)/(1−c)+cⁿQ, while Never has payoff A/(1−c). Their supremum
is exactly the displayed maximum, including c=0 and negative values.

If c(y)=1, all opponents Continue, A(y)=0, and own singleton sᵢ≤x. For
x≥0, all-Never opponents have cap max{sᵢ,0}≤x. For x<0, the chosen root's
objective is max{sᵢ,x}=x; since it MINIMIZES, Φ(x)=x. Monotonicity then
gives Φᴴ(0)≥Φᴴ(x)=x for every H, contradicting ℓᵢ<x. This excludes precisely
the problematic all-Continue/negative-boundary case. It does not incorrectly
select x as an executable negative Never payoff.

Thus Pᵢ≤x for every x>ℓᵢ, proving Pᵢ=ℓᵢ and ω(H)→0. Neither the
unrestricted infimum nor a stationary optimal punishment is assumed attained;
η-optimal punishment is enough.

## 4. Single exceptional deleted-survival coordinate

At t=N−H let sⱼ be j's probability of not quitting before t, and let
Dᵢ=∏[j≠i]sⱼ. For distinct players,

    DᵢDⱼ=R_p(t)∏[k≠i,j]s_k ≤ R_p(t)<ρ.

Hence at most one coordinate has Dᵢ>√ρ. If none does, replace the whole
suffix by all Never. Otherwise select the unique exceptional owner i* FROM
THE GIVEN LAW BEFORE PLAY, and replace the suffix by an η-optimal punishment
of i*. Give i* any prescribed continuation, for example Never.

This is one fixed calendar-dependent behavioral profile. The switch occurs
whenever play is still alive at date t; it is not conditional on identifying
a deviator. Each player keeps its original pre-t hazards. If an original
player has zero own survival to t, its previously unspecified off-path tail
can still be replaced; this does not alter the pre-t strategies. For the
exceptional player all opponent survival factors are positive, since
D_i*>√ρ>0, so its required opponent suffix conditioning is well-defined.

Prescribed payoff changes are bounded by 2MR_p(t)<2Mρ, because prescribed
play can see the new suffix only after JOINT survival. This is distinct from
the deleted survival relevant to unilateral caps.

## 5. Comparison to the OLD FINITE menu, not an unrestricted old cap

Write Bᵢᴺ(p) for the old finite-menu cap. Its Nash inequality is exactly
Bᵢᴺ(p)≤Uᵢ(p)+e. Let Lᵢ be the unconditional expected reward from opponents
quitting before t while i Continues throughout that prefix.

For a nonexceptional i, every new deviation quitting before t retains its
old finite-menu payoff. Every new deviation continuing to t has payoff at
most Lᵢ+DᵢM, whereas the OLD Never action has payoff at least Lᵢ−DᵢM.
Thus the NEW unrestricted cap is at most Bᵢᴺ(p)+2MDᵢ, hence at most
Bᵢᴺ(p)+2M√ρ. The comparison does not require an old late-date action or
any bound on the old unrestricted cap.

For i*, its old conditional opponent suffix is a product law on the
H-date menu. An optimal response on that suffix can be lifted to an old
absolute finite date t+a<N, or to Never. Therefore

    B_i*ᴺ(p) ≥ L_i*+D_i* m_i*(H).

Every new deviation continuing to t gets at most
L_i*+D_i*(P_i*+η). Early finite dates remain unchanged. Taking the larger
of these cases gives

    B_i*(p̂) ≤ B_i*ᴺ(p)
               +D_i*(P_i*+η−m_i*(H))₊
             ≤ B_i*ᴺ(p)+ω(H)+η.

The positive part is necessary when finite punishment values approach P
from above. Combining these cap bounds with the prescribed-payoff bound
proves (1). Since the only unabsorbed public history is all Continue, any
unrestricted unilateral behavioral payoff is an average of deterministic
finite stopping-time and Never payoffs. All such deviations are covered.

## 6. Useful immediate consequences, without a producer

First, long finite-menu near-equilibria have an UNCONDITIONAL punishment
floor. At their own deadline N,

    Uᵢ(p) ≥ mᵢ(N)−e ≥ Pᵢ−ω(N)−e.                  (3)

This follows because every opponent finite law has finite cap at least the
finite punishment minimum. It needs no no-UE assumption, no extracted exact
Bellman spine, and no conditional reach estimate. At a conditioned suffix,
one still must use its actual conditional Nash error, not the ex-ante e.

Second, let Γ>0 be a uniform lower bound on FULL terminal exploitability
of EVERY behavioral profile of the game. The completion theorem implies

    ∃H≥1, e*>0, ρ>0, ∀N≥H, ∀p∈F_N(e*),
        R_p(N−H)≥ρ.                                (4)

Choose H with ω(H) small, a small η, then e* and ρ so that the right side
of (1) is strictly less than Γ. A source violating (4) would complete to
a profile contradicting the gap. This is valid for ANY finite number of
players and arbitrary reward signs, directly from the terminal gap.

For Fin4 it supplies a shorter and more general proof of the robust
final-window conclusion in my approximate-source notebook. It does not
produce a source violating that conclusion. Likewise, (1) turns a SUPPLIED
family with vanishing e, joint reach, and ω(H) into full terminal approximate
Nash profiles; it does not manufacture the family.

## 7. Narrow source comparison and novelty assessment

Exact definitions and declarations inspected:

- `quittingBestReplyValue`, `quittingPunishmentValue`,
  `quittingStationaryPunishmentValue`, `quittingBestReplyValue_stationary`,
  `quittingPunishmentValue_eq_stationaryPunishmentValue`, and
  `quittingPunishmentValue_le_max_solo` in
  `UniformEquilibrium/Quitting/Stationary/MinMax.lean`.
- `quittingStationaryUnilateralCap`, its Bellman equation, and the fixed-row
  finite Snell convergence interface in
  `UniformEquilibrium/Quitting/Stationary/SnellCap.lean`.
- `IsQuittingRetainedTailFiniteTimingNash`,
  `quittingPureTimeDeviationPayoff_retainedTail_eq_of_lt`,
  `IsQuittingRetainedTailFiniteTimingNash.replacementBestResponseValue_le`,
  `.hostPunishmentDebt_le`, and `.punishmentDebt_le` in
  `UniformEquilibrium/Diagnostics/Quitting/RetainedTailFiniteTimingNash.lean`.
- `terminalGap_retainedTailFiniteTimingNash_jointReturn_ge` in
  `UniformEquilibrium/Diagnostics/Quitting/RetainedTailFiniteTimingReturnFloor.lean`.
- `literalRootStack_debt_le_referenceDebt_add_transmittedSeams` and
  `growingWord_referenceSeams_completion` in
  `UniformEquilibrium/Quitting/Root/FiniteWordSemanticSplice.lean`.
- The scope and source hypotheses of the existing one-isolated-owner cycle
  completion in `UniformEquilibrium/Quitting/Punishment/CompletedCycle.lean`.

The stationary punishment equality, one preselected exceptional punishment,
and joint/deleted-survival splice estimates are existing ingredients. The
checked retained-tail return floor instead assumes an exact retained-tail
timing Nash certificate and a supplied tail lying above actual punishment
caps. Fixed-row finite Snell convergence does not by itself justify swapping
an infimum over changing product profiles with H→∞.

Within this bounded search, the source's combination is genuinely sharper:
finite-menu punishment convergence supplies the exceptional owner's OLD
FINITE-menu comparison without a retained-tail punishment-floor premise.
The resulting quantitative same-prefix completion accepts ordinary finite
e-Nash data, arbitrary reward signs, and any finite player set. This is a
new direct source adapter relative to the inspected interfaces, not a new
stationary punishment theorem and not an early-absorption producer.

My earlier Sections 11–12 in
[`CODEX_RENY__APPROXIMATE_FINITE_TIMING_NASH_AND_REACH.md`](../notes/CODEX_RENY__APPROXIMATE_FINITE_TIMING_NASH_AND_REACH.md)
obtained a finite-menu floor and robust final-window result using a Fin4
no-UE compact-spine/forward-packet argument. Equations (3)–(4) here supersede
those particular proof dependencies. They do not close their missing
low-reach producer or invalidate the exact-finite-Nash incompleteness no-go.

The source's final counterexample to UNCHANGED extension also checks out:
player 1 has finite cap and payoff 1, while the newly admitted late date
pays 3/2 despite zero prescribed survival after its original sure Quit.
The completion changes the tail exactly where that unchecked deviation can
see it. No unresolved mathematical objection remains in the claimed scope.
