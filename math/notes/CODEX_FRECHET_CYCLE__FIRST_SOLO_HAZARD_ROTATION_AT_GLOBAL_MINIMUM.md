# First-solo hazard rotation at a global minimum

Identity: CODEX_FRECHET_CYCLE.

## Status and exact question

Ordinary mathematics, not independently reviewed or Lean-checked. This
tests a distinct actual operation after the two-helper coefficient test in
[the clock-copy note](CODEX_FRECHET_CYCLE__NORMAL_OWNER_CLOCK_RESAMPLING_AND_FULL_CAP_ACCOUNT.md).
The result below rules out the SMALL-first-hazard version using the
genuine source's cap margin and same-weight near-activity. It is not a
counterexample to Fin4, a new raw-table existence class, or a rejection
of all joint clock changes. The macroscopic first-hazard case is further
restricted in Section 3, but has not yielded a full-profile improvement.

Fix four-player rewards |r_i(S)|≤M, M>0, with zero Never payoff. Let p
be an actual independent finite-calendar source. Its first actual active
date t has only one positive Quit hazard, owned by k, with 0<h<1. Every
earlier date is silent. All original independent conditional tails after
t are retained, including every hidden response tail.

Choose ANY receiver b≠k. For a parameter 0≤x≤h, replace the date-t
hazards by

    q_b=x,       q_k=(h−x)/(1−x),       q_i=0 otherwise.       (1)

The root is independent, and its joint Continue probability stays
exactly 1−h. This changes the donor law as well as the receiver law. It
is not two additive clips or a correlated reassignment of the winner.

Can some x>0 lower the source's full exploitability? For small h the
answer is NO in the precise source regimes below.

## 1. Exact inherited receiver-cap branch

Write c=1−h, s=s_b, A=r_b({k}), J=r_b({k,b}), and let u and B̄ be
b's prescribed payoff and unrestricted cap in the ACTUAL original tail.
Before the change its date-t Quit and entire late cap branches are

    Q=c s+h J,          V=h A+c B̄.

Earlier silent responses, if there are any, give s. Every response after
t, including Never, is in V. Thus the original full cap B_b is the
maximum of these branches. Suppose the source supplies a margin

    B_b−s≥σ>0,          h≤σ/(4M).                         (2)

Because Q−s=h(J−s)≤2Mh≤σ/2, neither Q nor an earlier singleton
response attains B_b. Therefore B_b=V. This cap is a supremum over
complete responses; no attainment of a particular tail deadline is used.

Set C=J−A. The new root's terminal probabilities are

    {k}: h−x;
    {b}: x c/(1−x);
    {k,b}: x(h−x)/(1−x);
    Continue: c.

The receiver's prescribed-payoff increment is exactly

    ΔU_b = x/(1−x)[c(s−A)+(h−x)C].                    (3)

When b deviates, its NEW prescribed root hazard disappears, while k's
reduced hazard remains. Consequently b's inherited full late cap is

    V'=((h−x)/(1−x))A + (c/(1−x))B̄.

Subtracting (3) gives the exact increment of this COMPLETE gain branch:

    (V'−U'_b)−(B_b−U_b)
       = x/(1−x)[B_b−Q+x C].                         (4)

There is no unidentified response term here. The old tail cap B̄ remains
literal, so grand or triple outcomes hidden after deleting an old proper
clock are already included. Every new joining response can only increase
the new cap beyond this lower bound.

From (2), B_b−Q≥σ−2Mh, while C≥−2M and x≤h. Hence

    d_b(p_x) ≥ d_b(p)+x/(1−x)(σ−4Mh) ≥ d_b(p).       (5)

The bound applies to EVERY receiver and every x∈[0,h] whenever the
uniform source margin (2) is available. It does not use a favorable
singleton or pair sign. Reducing the donor's hazard exposes the receiver's
late cap faster than this small root can pay for it.

## 2. Consequence for the actual same-weight near-global sources

Suppose the original SAME tester probability λ satisfies

    Σ_a λ_a(E−g_a)≤a,       θ_i:=Σ_τ λ_(i,τ)≥θ₀>0.

Because every i-owned gain is at most d_i, one has

    d_i≥E−a/θ_i≥E−a/θ₀.

Together with (5), this yields the uniform, source-level conclusion

    E(p_x) ≥ E(p)−a/θ₀             for ALL b≠k and x∈[0,h]. (6)

The retained fixed-table sources have E→Ω>0, a→0 and θ₀ bounded below.
They also have a uniform cap-minus-singleton margin σ>0. On the branch
where their first solo hazard satisfies h≤σ/(4M), (6) rules out a fixed
full-regret improvement by ANY such rotation, even if its receiver and
strength are chosen anew from the complete source. This is not a claim
about an attained minimizer that the source may fail to supply.

For an actually attained positive global MAX minimum, the checked moat
gives σ=Ω, and the ordinary all-player-tie theorem gives d_b=Ω. Then
(5) directly says E(p_x)≥Ω; it is strict when h<Ω/(4M) and x>0.
This attained specialization is separate from (6).

Neither total singleton pressure nor reward-coordinate normality is
needed. Their absence from the selected source has not been repaired by
an assumption. The complete source directional inequalities remain true
but cannot overturn the explicit available-response lower bound (5).

## 3. The macroscopic-head test: a literal inherited-deviation floor

The receiver obstruction extends beyond the small-h estimate. Under ANY
rotation (1), let b deviate by keeping its NEW date-t randomization x
unchanged and replacing only its continuation law by a near-best response
in the unchanged actual tail. All rewards from root absorption are
unchanged by this deviation. Joint Continue probability is still c, so
its gain tends to

    c(B̄−u)=V−U_b.                                   (7)

This is a literal independent behavioral deviation, not a hypothetical
cap annotation. Therefore d_b(p_x)≥V−U_b for every x, regardless of
collision signs. In particular, whenever the original receiver's full
cap is its late branch B_b=V, its full debt cannot decrease under ANY
strength of this rotation. All hidden tail behavior is retained in B̄.
The same near-activity argument as (6) then prevents a fixed full-E
improvement on the genuine source sequence. No small-h hypothesis is
needed for this continuation-active receiver case.

For completeness the remaining receiver-only envelope is exact. Suppose
instead Q>V, put D=Q−V>0 and C=J−A, and compare to its old debt Q−U_b.
The changes in the new Quit and late branches respectively are

    −xC,                 (−D+x²C)/(1−x).            (8)

If C≤0, the Quit branch alone prevents any receiver-debt decrease.
If C>0, both displayed branches are strictly below the old debt exactly
when 0<x and x²C<D. Earlier silent singleton responses are strictly
below the old cap by the source margin and remain so for small enough x.
Consequently this receiver's debt can decrease somewhere along the
rotation only when it is a STRICTLY date-t-Quit-cap-active collider:

    Q>V,                  r_b({k,b})>r_b({k}).        (9)

This is a classification of the tested receiver envelope, NOT a producer
of such a receiver. The normal-owner affine-rate restriction compares
the Quit premium with r_b({k}); it does not compare Q with the actual
hidden-tail cap V. Same-owner near-activity does not supply the missing
strict inequality Q>V either. Even if (9) holds, (8) has not controlled
the donor or the two untouched owners' new joining branches, so no full-E
decrease follows from the criterion.

The direct survival-preserving test stops at this point. Its exact
inherited-deviation floor (7), not another unsigned multiplier inequality,
explains why the continuation-active source branch cannot be improved
this way. The original unrestricted global-minimum condition has not
been replaced by a local hypothesis or falsified by an example.

## 4. Scope, sources, and next test

The source's uniform cap margin and all-owner near-activity are supplied
by the ordinary
[singleton-fiber source reduction](../exports/MEMBERSHIP_STRETCH_AND_SINGLETON_FIBER_SOURCE_REDUCTION.md)
and its fixed-table/silent-source transport. In particular this argument
does not infer a margin from a singleton outcome count. The underlying
checked declaration is `minimumTerminalSemantic_exploitabilitySingletonMargin`
in `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticPlateauDynamicCostate.lean`.
It is a global MAX semantic-carrier statement, not a total-debt or
fixed-calendar-minimum theorem. The all-player-tie argument used only in
the attained specialization appears in the
[frozen inverse-stretch packet](../exports/INVERSE_MEMBERSHIP_STRETCH_SURE_CORE_SIGN_REVERSAL.md).
It is now also a checked unit-cube declaration,
`minimumTerminalSemantic_maximumDebt_allPlayersTie`, with its actual-profile
adapter `quittingTerminalDeviationDebt_eq_exploitability_of_attained_positive_minimum`,
in `UniformEquilibrium/Diagnostics/Quitting/PositiveMaximumDebtMinimum.lean`.
That file and its explicit MAX, unit-bound and global-attainment hypotheses
were read. The arbitrary-M ordinary statement used here follows by positive
uniform reward scaling; it is not a claim that the displayed Lean theorem
omits its unit-bound hypothesis.

The first-active-row condition matters: after a nontrivial common prefix,
prescribed and deviating reaches differ and (4) needs additional factors.
The h=1 boundary has a different feasible rotation geometry and is not
covered. The source need not be singleton-only after t. The proof does
not change or discard any tail, and earlier silent singleton responses
were retained when identifying the old cap.

For the two untouched owners the root's joint Continue probability is
unchanged, so every strictly later response gain is exactly invariant.
That fact alone cannot prove improvement; (5) identifies the changed
receiver's unavoidable exposed cap in the small-h branch.

The next distinct head operation, if pursued, must allow net GREATER
absorption rather than keeping c fixed: jointly lower the donor hazard
and activate one receiver, choosing q_k<h and q_b>0 with
(1−q_k)(1−q_b)<1−h. This contracts the inherited tail-deviation floor
while still creating at most two prescribed root quitters, hence no NEW
grand-coalition tester at that first row. It is different both from two
additive helper clips and from (1). All old hidden grand tails, both
changed owners' caps and the two untouched joining testers remain. No
choice of these two hazards or improving profile is yet proved.

## 5. Increased-absorption head test stopped at the existing root budget

The proposed continuation of Section 4 was checked against the actual
production declarations before expanding its algebra. The universal
`quittingTerminalSemanticDebt_prefix_le_auxiliaryNashDefect` and its
zero-defect specialization `quittingTerminalSemanticDebt_prefix_le_auxiliaryNash`
in `UniformEquilibrium/Quitting/Terminal/AuxiliaryNashDebt.lean` already
retain the relevant cap-versus-payoff and root-defect terms. At an exact
root against the ACTUAL tail payoff u, they give

    d'_i≤a_i(q)δ_i,

where δ_i=B̄_i−u_i is the actual tail debt and a_i is opponents'
Continue probability, not joint Continue probability. At a first-solo
attained MAX source, all-player ties and U_k≥s_k give δ_k≤Ω, while
the available late response gives δ_i≤Ω/(1−h) for i≠k.

Thus a two-active root with greater joint absorption contracts the two
untouched owners' inherited bounds. But decreasing q_k below h increases
the RECEIVER'S factor a_b=1−q_k. Increasing b's own hazard cannot decrease
that factor. The exact-root budget therefore leaves precisely the
unsigned receiver bill already identified by the earlier cap/payoff
account. Choosing an arbitrary root merely adds its literal coordinate
Nash defects; the source has not supplied bounds paying those defects.

The MAX near-minimum theorem
`nearMinimumTerminalSemantic_exploitabilityAuxiliaryNash_absorptionMass_le_sharp`
and the exact MAX auxiliary moat in
`UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticPlateauDynamicCostate.lean`
were read directly. They require the INPUT continuation pair itself to be
near the global MAX minimum and exact Nash play at the specified lower-cap
continuation. Our unchanged tail need not be near that minimum, and the
two changed hazards are not asserted to be such a Nash root. Consequently
those theorems do not orient this proposed replacement.

The declarations `minimumTerminalSemantic_auxiliaryNash_budget` and
`minimumTerminalSemantic_weightedAuxiliaryNash_budget`, in the respectively
named files under `UniformEquilibrium/Diagnostics/Quitting/`, instead
assume a global minimum of TOTAL or a fixed weighted SUM of debts. The
SAME tester multiplier is not such a weighted-global-minimum certificate.
These budget hypotheses cannot be transferred either to the MAX source
or to its selected actual tail.

RENY's [actual-payoff root-uniqueness note](CODEX_RENY__MAXIMUM_DEBT_MINIMUM_TIES_AND_ACTUAL_ROOT_UNIQUENESS.md)
was read in full and makes the same objective distinction. It does not
give a nontrivial root at an arbitrarily selected suffix payoff. This
head test therefore stops without another ledger, conditional consumer,
or export proposal. The next operation must modify the opponent laws
across the actual calendar, rather than relying on a fixed-tail one-row
absorption change.
