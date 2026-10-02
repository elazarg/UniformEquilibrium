# Sure-host completion on the fixed singleton fiber

Author: CODEX_NOETHER_SUPPORT.

Status: bounded ordinary-mathematical source test, not Lean checked. The
complete-cap calculation is exact. Its zero-debt entrance is the existing
punishment-vector sure-root condition. The retained singleton-fiber maximum
does not furnish the needed upper comparison. No new producer or counterexample
to the global conjecture is claimed.

## 1. Exact question and source

Let I={0,1,2,3}, with independent private stopping clocks in the nonnegative
integers together with Never. Rewards r_i(S) lie in [−1,1] for nonempty S;
Never pays zero. Every cap below is over all unilateral behavioral responses.
Write U_i for prescribed terminal payoff, B_i for the full cap, and

    d_i=B_i−U_i,   E=max_i d_i,   η(r)=inf_actual_profiles E.

The source is the final table in the reviewed membership-stretch reduction:
all 56 non-own-singleton coordinates b are fixed, the four coordinates
s_i=r_i({i}) range freely in [−1,1], and the selected s maximizes η(b,s)
on this fiber, at a positive value m. In the three-sure leaf, an actual
unpadded date-zero root q* attains E(q*)=m. Its complete E is independent
of all four own singletons, so

    η(b,t) ≤ E_(b,t)(q*) = m   for EVERY t in [−1,1]^4.       (1)

The proposed finite operation retains one host h surely at date zero and
reselects the other three independent root laws as a Nash equilibrium.
Can the fiber maximum force one such completion to have E<m?

## 2. The correct three-player game is constant on the whole fiber

For fixed h, each nonhost i chooses Quit or Continue at date zero, and
receives r_i({h}∪T), where T is the set of nonhosts choosing Quit. Let N_h
be the mixed Nash set of this finite three-player game. It is nonempty
and compact. It depends only on b, not on ANY own singleton coordinate:
every coalition in this game's i-coordinate contains h≠i.

This is not the deleted game on I\{h}. In particular, the host-release
failure in [SPINOZA's note](CODEX_SPINOZA__HOST_RELEASE_THREE_PLAYER_NASH_LIFT_SIGN_REVERSAL.md)
does not by itself falsify this operation. That note re-equilibrates a
host-excluding child game; this operation keeps h in every prescribed
date-zero outcome.

Fix any x∈N_h. All expectations below use its literal product law on T.
Set

    C=Pr(T=∅),
    Q₊=Σ_(T≠∅) Pr(T) r_h({h}∪T),
    H=Σ_(T≠∅) Pr(T) r_h(T),
    A=H−Q₊.

Prescribed host payoff is Q=C s_h+Q₊. With literal Never after this root,
the complete host cap and debt are

    B_h=max(Q, H+C max(s_h,0)),
    d_h=[A+C max(−s_h,0)]₊.                                 (2)

Indeed, Quit at zero pays Q. Every positive finite date pays H+C s_h,
and Never pays H. There is no earlier date. A randomized stopping law
cannot exceed the maximum of these pure responses. The other three
full debts are exactly zero: h's sure root screens every nonhost
unilateral response, and the two root endpoints are already Nash.

No assertion here that merely padding this root would preserve (2).
Padding can introduce the host's earlier own-singleton response.

## 3. Best hidden tail and the existing consumer

Let P_h be h's punishment value: the infimum, over actual independent
opponent continuation profiles, of h's unrestricted best-response cap.
For a chosen continuation with cap K_h, the exact root-then-tail formula is

    B_h=max(Q, H+C K_h),
    d_h=[A+C(K_h−s_h)]₊,    d_i=0 for i≠h.                  (3)

When C=0 the tail is irrelevant. When C>0, conditioning on every
nonhost continuing at zero leaves their separately chosen tail laws
independent. This is a legal behavioral construction, not conditioning
play on a private joint event. Under prescribed play the tail is never
reached, since h quits surely. Under any single nonhost deviation it
still is not reached. Under h's Continue response its cap is exactly
the conditional K_h in (3).

Infimizing over actual tails, without assuming punishment attainment,
gives the exact best-completion value

    Φ_h(s_h)=min_(x∈N_h) [A(x)+C(x)(P_h(s_h)−s_h)]₊.         (4)

Consequently η(b,s)≤min_h Φ_h(s_h). If Φ_h(s_h)=0, compactness
of N_h supplies a root with h sure, all nonhost root defects zero, and
host root defect zero at continuation P_h. The other continuation
coordinates do not enter any nonhost response because h is sure.
Thus this is precisely
`HasQuittingPunishmentVectorNashRootWithSureQuitter`, not a new source
criterion. Its checked consumer produces a fixed-payoff uniform
equilibrium using arbitrarily accurate actual punishment tails.

The single-anchor dominance theorem is another sufficient entrance to
this construction: its pointwise bound on all host-excluding outcomes
controls the host cap. That extra bound is not supplied by fiber
maximality. No membership or anchor-dominance assumption is made here.

## 4. What changing the host singleton actually does

Only s_h affects P_h within the four-coordinate fiber. For t≥u, any
fixed opponent law and any host response have payoff increment between
0 and t−u, since the changed reward multiplies the probability of the
single terminal event {h}. Taking the supremum over responses and the
infimum over opponent laws preserves these bounds:

    0 ≤ P_h(t)−P_h(u) ≤ t−u.                                (5)

Therefore P_h(t)−t is nonincreasing and continuous. As N_h, A, and C
are constant on the entire fiber, Φ_h is likewise nonincreasing and
continuous. Equation (4) retains ALL completion equilibria; this is
not a bad selected-branch test or an equilibrium-component continuation
assumption.

At the selected positive source, however, (1) and (4) say only

    m=η(b,s) ≤ Φ_h(s_h),
    η(b,t) ≤ min(m, min_h Φ_h(t_h)).                          (6)

Decreasing the upper envelope Φ_h by raising t_h can lower η(b,t).
That is consistent with, not contrary to, maximality at s. In
particular one cannot insert η(b,t)≥m into (6), nor use the old
three-sure root's unchanged value as that missing lower bound.

At the same selected table, every literal finite-tail completion in
(3) actually has E>m: E<m contradicts global minimality, while E=m
would be an attained positive global minimum with three zero debts,
contrary to the all-player-ties theorem. This strict statement is
pointwise in actual completions; it does not assert that the infimum
in (4) is attained by an actual punishment tail or has a uniform gap.

## 5. Exact boundary and inspected sources

The operation is a legal independent one-root modification, with a
complete host cap. It does not select an improvement from the retained
fiber source. The unsupplied comparison is an upper bound Φ_h(s_h)<m
at the SAME maximizing s, or a justified different-table lower bound
that would make a decreased Φ_h contradictory. Neither follows from
the monotonicity in (5) or the maximum in (1).

Named declarations inspected:

- `HasQuittingPunishmentVectorNashRootWithSureQuitter` and
  `quittingInstantPunishmentεEquilibriumExistence_iff_sureQuitterPunishmentVectorNashRoot`
  in `UniformEquilibrium/Quitting/Classification/InstantPunishmentSureQuitterCharacterization.lean`.
- `quittingPunishmentSureRootTarget_isUniformEquilibriumPayoff_and_floor`
  in `UniformEquilibrium/Quitting/Classification/InstantPunishmentSureQuitterPayoff.lean`.
- `QuittingSingleAnchorInducedDominance`,
  `exists_exactTerminalNash_and_uniformPayoff_of_singleAnchorPoint`, and
  `exists_exactTerminalNash_and_uniformPayoff_of_singleAnchorMembership`
  in `UniformEquilibrium/Diagnostics/Quitting/Collision/Toggles/SingleAnchorArbitraryCompletionEscape.lean`.

The ordinary all-player-ties and source-fiber facts are recorded, with
their exact source scope, in the frozen
[three-sure packet](../exports/THREE_SURE_MINIMA_REQUIRE_OPPOSED_MEMBERSHIP_REVERSALS.md).
No external uncommitted Lean file is used to upgrade their trust status.

Next question: find a global different-table comparison that controls
the lower side of (6), or change the finite operation. Do not develop
another sure-root wrapper or replace this missing comparison by a
chosen child equilibrium's local sign.
