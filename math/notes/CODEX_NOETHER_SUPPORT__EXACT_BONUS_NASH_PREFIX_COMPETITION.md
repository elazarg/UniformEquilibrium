# Exact solo-prefix competitors for the full bonus-Nash objective

Author: CODEX_NOETHER_SUPPORT.

Status: proved conditional competing-law operation in ordinary mathematics,
not Lean-checked or exported. It acts on literal finite auxiliary Nash laws
and controls every ORIGINAL unilateral response. It is not an arbitrary-data
producer or a new UE class. The exact-zero-owner source and nonsummable
renewal requirements remain unresolved.

## 1. Full objective and exact source screen

Fix a complete canonical Fin4 table r with own singletons s=(1,0,0,0),
bounded real terminal rewards, zero Never, and independent private clocks.
The finite menu is F_N={0,...,N−1,Never}, N≥1. An auxiliary game adds ξ_j
only to player j's own PLANNED Never action. Finite-action rewards do not
change. For δ≥0 let G_(N,δ) be ALL exact auxiliary Nash pairs (ξ,p) with
ξ∈[0,δ]^4. Write U_j, B_j, d_j=B_j−U_j for original prescribed payoff,
FULL behavioral cap, and debt, and E=max_j d_j. The objective remains

    A(N,δ)=min_(ξ,p)∈G_(N,δ) E(p),

not a deleted-survival or auxiliary-payoff objective. For a source define

    z_j=p_j(Never), u_j=U_j+ξ_j z_j, C=max_j ξ_j z_j≤δ.

The u_j are auxiliary Nash payoffs and menu cap values. C is a proof ledger,
not a substitute objective. The exact union-of-Nash characterization and the
open joint-selection question are in the
[actual-output notebook](CODEX_NOETHER_SUPPORT__BONUS_NASH_ACTUAL_OUTPUT_EXACTIFICATION.md).

Assume a NONPIVOT i∈{1,2,3} has auxiliary value u_i=0=s_i EXACTLY. For
j≠i put v_j=r_j({i}), k_j=r_j({i,j}), g_j=u_j−s_j, a_j=k_j−v_j.
Suppose h∈(0,1] satisfies

    h a_j≤(1−h)g_j                 for every j≠i.       (S)

This tests raw singleton/pair rewards and the actual source auxiliary
payoff. If all g_j>0, some h>0 works. If g_j=0, positive h requires a_j≤0.
Negative g_j are retained: (S) may require a large h or be infeasible.

## 2. Literal competing laws and exact auxiliary Nash

Shift each source finite time by one, keeping Never. Every nonowner uses
that shifted law. Owner i privately quits at the new date zero with
probability h, otherwise using its shifted source law. Independence is
preserved and all laws belong to F_(N+1). Set

    z'_i=(1−h)z_i,       z'_j=z_j for j≠i;
    ξ'_i=ξ_i,           ξ'_j=(1−h)ξ_j for j≠i.          (12)

These bonuses remain in [0,δ]^4. For a nonowner j, every shifted old finite
response and Never with its new bonus is the image of its old auxiliary
value under x↦h v_j+(1−h)x. Thus every old supported action remains best
among shifted actions. The new Quit0 pays h k_j+(1−h)s_j, which is at most
h v_j+(1−h)u_j by (S). Its prescribed law is exact auxiliary best response.

Against owner i, every opponent waits at the new date. All shifted old
response values, including the unchanged ξ_i for Never, are identical to
their source values, with old auxiliary cap zero. New Quit0 also pays zero.
Both the added atom and retained supported actions are therefore optimal.
This proves (ξ',p')∈G_(N+1,δ). The reasoning includes h=1: all shifted
nonowner values then coincide and (S) becomes k_j≤v_j.

## 3. Complete original cap contraction

Every nonowner response either quits at new date zero or waits and then
uses an arbitrary old stopping law. Therefore its original full cap and
prescribed value are exactly

    B'_j=max(h k_j+(1−h)s_j, h v_j+(1−h)B_j),
    U'_j=h v_j+(1−h)U_j.                              (13)

The supremum need not be attained; the affine image of the old supremum
is still the waiting-response supremum. By (S) and u_j−U_j=ξ_j z_j,

    d'_j≤(1−h)max(d_j,ξ_j z_j)                 (j≠i).   (14)

For the owner, every response after the old finite menu equals Never
because s_i=0. Its original FULL cap thus equals its original menu cap and
is at most its auxiliary cap u_i=0. New Quit0 guarantees zero while all
waiting responses have cap B_i≤0. Consequently

    B'_i=0, U'_i=(1−h)U_i=−(1−h)ξ_i z_i,
    d'_i=(1−h)ξ_i z_i.                                (15)

All four complete caps and the coordinatewise bonus-credit identities give

    E(p')≤(1−h)max(E(p),C),
    C(p',ξ')=(1−h)C.                                  (16)

Thus E(p')≤(1−h)max(E(p),δ), with no omitted nonpivot deviation. The credit
ledger is only a bound used in the proof; the selected objective remains E.

The actual pivot late gain also scales EXACTLY. With
D_0=∏_(j>0)z_j, W_0 its Never response, and L_0=W_0+D_0−U_0,

    D'_0=(1−h)D_0,
    W'_0=h r_0({i})+(1−h)W_0,
    U'_0=h r_0({i})+(1−h)U_0,
    L'_0=(1−h)L_0.                                    (17)

In particular, if the source minimizes A(N,δ)>δ, then

    A(N+1,δ)≤(1−h)A(N,δ)<A(N,δ).                      (18)

This is a genuine exact competing law at a full-objective minimizer
whenever (S) and the zero-owner equality hold.

## 4. Small exact VANISH test

For completeness the test's full table is as follows. Pivot 0 gets one if
it belongs to the nonempty coalition and two otherwise. For each nonpivot
j in the cycle 1→2→3→1, its payoff is zero if j quits, minus one if j
does not quit and 0 does, and otherwise
2·1_(pred(j) quits)−1_(succ(j) quits). Never is zero.

Use N=3, pivot Never, and let nonpivots 1,2,3 quit at dates 0,1,2,
respectively, with probability one half, otherwise Never. Their complete
pure response rows at dates (0,1,2,3,Never) are

    player 0: (1, 3/2, 7/4, 15/8, 7/4);
    player 1: (0, 0, −1/2, 0, 0);
    player 2: (0, 1, 1, 3/4, 3/4);
    player 3: (0, −1/2, 0, 0, 0).

All later finite responses equal date 3. Hence

    ξ=(0,0,1/4,0),   z=(1,1/2,1/2,1/2),
    u=(7/4,0,1,0),   U=(7/4,0,7/8,0),
    B=(15/8,0,1,0),  E=C=1/8.

The source is exactly auxiliary Nash by these rows. For owner i=3 the
three (a_j,g_j) pairs are (−1,3/4), (−2,0), (1,1), so h=1/2 passes (S).
The four-date competitor has

    ξ'=(0,0,1/8,0),       u'=(15/8,1,0,0),
    U'=(15/8,1,−1/16,0),  B'=(31/16,1,0,0),
    E'=C'=L'_0=1/16.

These exact caps follow from (13)–(15). The newly available player-2
Quit0 constraint is tight, not omitted. The source is the already known
VANISH law from
[RENY's coupled construction](CODEX_RENY__PIVOT_LP_AND_FINITE_NONPIVOT_BEST_REPLY_COUPLING.md)
and [HILBERT's selector](CODEX_HILBERT__VANISHING_PRIVATE_NEVER_BONUS_SELECTOR.md).
This test verifies cross-horizon auxiliary-Nash competition, not a new
existence class or a new independent VANISH producer.

## 5. What a positive global limiting minimum must avoid

Fix δ≥0 and put a_δ=inf_(N≥1) A(N,δ). Suppose a_δ>δ. Choose horizons and
their global actual-output minimizers with A(N_k,δ)→a_δ. If some fixed
h_*>0 were feasible at an exact zero-valued nonpivot along infinitely many
of these minimizers, (18) would imply

    a_δ≤(1−h_*)A(N_k,δ)→(1−h_*)a_δ<a_δ,

a contradiction. Hence such a sequence must eventually avoid zero-valued
owners admitting a uniformly positive screened prefix. This is an
unavoidable source-stratum condition, not a raw-table classification.

Neither existence nor renewal of that stratum has been proved. The equality
is u_i=0 EXACTLY, not u_i≤δ or u_i→0. If u_i>0, new Quit0 is inferior;
if u_i<0, a retained finite supported action of value u_i is inferior to
Quit0. Adjusting only Never cannot equalize a nonzero finite-action value
with opponents fixed. Global minimization has not been shown to supply
the joint reselection that reaches a screened zero surface without raising E.

Even one accepted step does not prove renewal. The new nonowner auxiliary
payoffs are u'_j=h r_j({i})+(1−h)u_j, while u'_i=0. This can spend the
other coordinates' screening slack or remove all useful zero owners. If
a legal sequence exists, (16) only forces vanishing debt when
∏_k(1−h_k)=0, equivalently when Σ_k h_k=∞ (unless some h_k=1). A sequence
of merely positive, summable hazards need not drive E to zero. No such
nonsummability or maintained-screen argument is presently supplied.

Next concrete question: can bonus/law variation at a full-objective global
minimum force a screened exact zero surface, or a different strict
competitor when all these screens fail, while preserving enough slack for
nonsummable renewal?

The narrow lookup examined the named RENY/HILBERT bonus notes, the frozen
auxiliary-descent packet, and the finite-menu/one-law mixture interfaces.
No identical private-bonus-rescaled prefix operation was found in that
lookup. The affine semantics agree with
`quittingTerminalPayoff_update_eq_expect_stoppingLaw_pureTime` in
`UniformEquilibrium/Quitting/Paths/BehaviorStoppingPayoff.lean`; the exact
menu distinction was inspected in `IsQuittingFiniteDeadlineNash` and
`isQuittingFiniteDeadlineNash_iff_pure` in
`UniformEquilibrium/Quitting/Terminal/FiniteDeadlineReplyCap.lean`. No new
Lean theorem or broad strategy-class completeness is claimed.
