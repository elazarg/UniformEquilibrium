# Bounded checkpoint: raw finite-menu minimax exchange

Reviewer/researcher: CODEX_FRECHET_CYCLE.

Status: method stopped at an existing correlation boundary. This is not a
new no-go theorem, positive selector, or negative answer to the finite-menu
question. No export or Lean work.

## Exact target and tested operation

For the canonical question's product-law domain X_N=∏_i Δ(F_N), N≥1,
let g_(i,t)(p) be the unrestricted pure-test gain. Tests are t∈F_N for
every player and additionally t=N for the pivot. The current production
identity gives

    f_N(p)=max_(i,t)g_(i,t)(p)=max(E_N(p),L_0(p)),
    m_N=min_(p∈X_N)f_N(p).

The desired conclusion is inf_N m_N=0. The proposed direct minimax exchange
would compare m_N to

    d_N=max_(λ∈Δ(tests)) min_(p∈X_N) Σ_(i,t)λ_(i,t)g_(i,t)(p).

Every fixed weighted expression is multilinear in the four marginal laws,
so its minimum over X_N occurs at a pure product vertex. Nevertheless the
maximum of these expressions is not jointly convex in the marginals.
The exact test below rules out identifying d_N with m_N.

## Canonical test and its precise quantifiers

Use the complete H table from
[the canonical homotopy note](../notes/CODEX_HILBERT__CANONICAL_PIVOT_BOUNDARY_HOMOTOPY.md):

    r_0(S)=1+1[2∈S] if 0∈S, and 3·1[2∈S] otherwise;
    r_i(S)=1[i−1∈S] if i∈S, and 3·1[i−1∈S]−1 otherwise,
             for i=1,2;
    r_3(S)=0 if 3∈S, and 1 otherwise.

Own singletons are (1,0,0,0); Never pays zero. Let μ be the equal lottery
over three PURE PRODUCT profiles: only player 0, only player 1, or only
player 2 quits at date zero; every other player plays Never. This lottery
is used only as an algebraic test, not implemented as behavioral play.

Its average prescribed payoff is (4/3,1/3,1/3,1). Its expected gains for
unconditional pure tests are exactly:

| player | Quit at 0 | Never | Quit at any t≥1 |
|---|---:|---:|---:|
| 0 | 0 | −1/3 | 0 |
| 1 | 0 | 0 | 0 |
| 2 | 0 | 0 | 0 |
| 3 | −1 | 0 | 0 |

For example, the pivot's late payoff is the average of 1, 0, and 3:
when its own prescribed singleton is removed, every opponent plays Never,
and the late test gets its singleton reward 1. This accounts for the omitted
date rather than dropping it.

For any λ, the minimum over pure product profiles is at most the μ-average,
which is nonpositive. Hence d_N≤0 for every N. Conversely player 3's Never
test has nonnegative gain at EVERY product profile: its terminal reward is
1 exactly when another player quits without it and is 0 whenever it quits.
Taking Never cannot reduce that payoff. Its minimum gain is zero. Thus

    d_N=0 for EVERY N≥1.                                      (1)

On the other hand m_N>0 for every fixed finite N. Here is a short reason
that does not assume subgame perfection at unreached histories. If a finite
product profile were full exact Nash, every reached current root would be
Nash against changing the current action and keeping the conditional tail.
No active player 0, 1, or 2 can quit surely: a sure active quitter forces
the next active player to Continue and the following one to Quit, making
the initial quitter prefer Continue. A sure player 3 either gains by
Continue when any active hazard is positive, or permits pivot Quit to gain
1 when all active hazards vanish. Thus every reached root has positive
joint Continue probability. Induction makes every finite date reached and
every player's Never mass positive. In an exact finite-menu Nash profile,
pivot Never support gives U_0=W_0. Its late gain is then the strictly
positive product of the three opponent Never masses. Contradiction.
Compactness of X_N and continuity of f_N therefore give

    m_N>0 for EACH fixed N.                                   (2)

There is NO positive common lower bound over all N in this example. The
same canonical note proves an exact unrestricted periodic equilibrium with
successive owners 0,1,2 and hazard 1/2. Censoring its finite-clock tails
gives product laws with full regret tending to zero. Thus

    inf_N m_N=0.                                             (3)

Equations (1)--(3) falsify the finite-N exchange, not the requested
deadline-asymptotic selection. A hypothetical vanishing product/dual gap
would still require an actual product-law selection proof; no such estimate
is supplied by classical minimax.

## Existing home and inspected source boundary

The relevant failure is already recorded in
[MERIDIAN_BLINDSPOTS](../notes/MERIDIAN_BLINDSPOTS.md), Section 5.6:
convexified controllers and no-regret methods return correlated distributions,
and independent product rounding with full cap control is not automatic.
[SNELL's aggregate note](../notes/CODEX_SNELL__AGGREGATE_PAID_ORIENTATION_FINITE_ATOM_AND_NORMALIZED_PASSPORT.md),
Section 7.30, similarly distinguishes actual response-hull outcome laws from
independent profiles and literal chronological returns. Its source-local
response hull is not identical to the raw dual above, but the unresolved
agency transition is the same. No new general infrastructure is needed.

The exact named production declarations read were
`singlePivot_fullExploitability_eq_max_menuExploitability_scalar` in
`UniformEquilibrium/Quitting/Terminal/SinglePivotFiniteMenuSource.lean` and
`exists_exactFiniteDeadlineTimingNash` in
`UniformEquilibrium/Quitting/Terminal/FiniteDeadlineNashExistence.lean`.
They respectively verify a supplied same-law scalar pair and produce fresh
exact menu Nash; neither performs this minimax exchange or controls L_0.

The two requested nearby failed attempts were also read completely:
[positive-bonus approximate completeness](../notes/CODEX_RENY__POSITIVE_BONUS_APPROXIMATE_COMPLETENESS_TEST.md)
does not preserve unrestricted responses and inner optimality under its
joint repair, while
[global MAX Never-arm release](../notes/CODEX_HILBERT__GLOBAL_MAXIMUM_JOINT_NEVER_RELEASE_BOUNDARY.md)
lacks the simultaneous head/deleted-tail cap comparison. Neither is a
universal no-go or supplies a premise for the present exchange.

The raw minimax-exchange method is stopped. No independently justified new
global variational operation is asserted at this checkpoint.
