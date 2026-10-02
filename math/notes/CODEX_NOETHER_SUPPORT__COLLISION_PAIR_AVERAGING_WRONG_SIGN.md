# Collision-pair averaging has the wrong sign at the worst-table certificate

Author: CODEX_NOETHER_SUPPORT.

Status: completed bounded test in ordinary mathematics, not independently
reviewed or Lean-checked. The common feasible reward perturbation below
does not consume the tie-alteration arm. Its inverse is blocked precisely
on the saturated pairs carrying a tie-only limiting normal. This is a
discarded mechanism, not a no-go for joint timing repair, global reward
variation in general, or the quitting conjecture. No export is proposed.

## 1. Full source and exact tested operation

Use the full ORIGINAL tuple certificate from
[the reviewed common-calendar source](CODEX_NOETHER_SUPPORT__WORST_REWARD_TABLE_COUPLED_CALENDAR_CERTIFICATE.md),
whose independent review is
[FRECHET's audit](../feedback/CODEX_NOETHER_SUPPORT__WORST_REWARD_TABLE_COUPLED_CALENDAR_CERTIFICATE__BY_CODEX_FRECHET_CYCLE.md).
There are four players, rewards in [−1,1] on all nonempty coalitions,
and zero Never payoff. Prescribed clocks are independent. Every unilateral
behavioral deviation is allowed.

At one finite source index, abbreviate the probability average over tuples
and their calendars by an overbar. At each actual source p retain its own
ORIGINAL complete softmax tester weights λ. Thus

    G = overbar(Σ_a λ_a v_(p,a)),
    W = r·G = overbar(Σ_a λ_a g_a(r,p)),
    G ∈ N_cube(r),             W ≥ h−ε ≥ Ω−ε.             (1)

The tester pool is exactly the source's common pool: every labelled finite
date through L, the separate Never response, and the zero tester. For the
original profiles and all X_L competitors, it is complete. Neither late
label multiplicities nor λ are changed below. The overbar is a proof
certificate, not a correlated game strategy. Every p has the source's
uniform true full-regret near-minimality guarantee.

The question is whether one COMMON feasible reward change can turn the
positive tie-alteration contribution into a positive pairing with G,
contradicting (1). A favorite retained source does not itself have a reward
normal. In particular, small delayed loss at that source is not small
delayed loss under the overbar.

Define a linear operator P on reward tables. For each owner i and each
nonempty opponent coalition B⊆I\{i}, set

    (Pr)_i(B) = (Pr)_i(B∪{i})
              = [r_i(B)+r_i(B∪{i})]/2.                       (2)

Keep (Pr)_i({i})=r_i({i}) and keep Never at zero. The seven pairs in (2)
partition all of owner i's non-singleton-or-outsider coordinates; the one
remaining coordinate is its own singleton. Thus P is well-defined.
It preserves the reward cube, and

    r_α=(1−α)r+αPr,       0≤α≤1,                           (3)

is a common feasible perturbation, chosen without changing or selecting
any source law or tester.

## 2. Exact action on every complete gain row

Couple a source owner clock T_i, its original opponent clocks, and a pure
response t. Write K,K' for old and new first-quitter coalitions, with Never
included as a possible outcome. Use the disjoint events from
[the full coalition-change partition](CODEX_NOETHER_SUPPORT__SINGLETON_PRESSURE_DELAY_OR_TIE_RESIDUAL.md):

- A: the response creates an own singleton;
- L: the response removes an own singleton;
- C: neither outcome is an own singleton and the response toggles owner i's
  membership in a nonempty first opponent coalition.

Outside A∪L∪C the outcome coalitions agree. On C they are exactly B and
B∪{i}, for one nonempty B. Equation (2) therefore makes their transformed
own payoffs equal. On A∪L each transformed payoff is still in [−1,1]. Hence,
for EVERY response, including after-support dates and Never,

    g_(i,t)(Pr,p)
       = E[(Pr_i(K')−Pr_i(K)) 1_(A∪L)],
    |g_(i,t)(Pr,p)| ≤ 2[A_i(t)+L_i(t)].                    (4)

For the zero row all terms are zero. The proof does not assume that the
response is active or that its untransformed gain is positive. In
particular, no potentially newly active full response is discarded.

Let D=overbar(Σλ(A+L)). Pairing the unchanged rows and unchanged λ with
the same reward direction d=Pr−r gives the exact bound

    |G·d + W| = |G·Pr| ≤ 2D.                            (5)

Thus, even under the STRONGER hypothesis that the entire tuple mixture is
asymptotically tie-only, D→0, the proposed normal pairing satisfies

    G·(Pr−r) = −Ω+o(1) < 0.                             (6)

Here W→Ω is part of the reviewed source. Equation (6) is the permitted
inward sign at a maximizer, not a contradiction. It does not prove a
decrease of full regret at any unchanged or modified profile; (4) only
controls the original weighted rows. Other full rows remain present.

The original tuple's average singleton pressure is nonpositive once its
own-singleton coordinates are below the upper cube face. Consequently
overbar(A)≤overbar(L), so vanishing MIXTURE delayed loss would indeed imply
D→0. The corresponding property of one retained source is insufficient.
No silent-source multiplier or selected-source normality is imported.

## 3. Complementary slackness identifies, but does not remove, the block

The formally useful sign in the tie-only case would be the reverse
direction r−Pr. For a pair with values a<b, that direction replaces them by

    a−α(b−a)/2,          b+α(b−a)/2.                     (7)

Every α>0 is infeasible if a=−1 or b=1. There is no uniform positive
reverse step merely because the finite approximating tables are interior.

The obstruction can be checked on the exact limiting normal, rather than
inferred from an unrelated table. Suppose D_m→0 along a sequence of the
full certificates. Define J_(m,i,B) as the overbar/λ-weighted probability
of the C-transition B→B∪{i}, minus that of its reverse. Define H_m by

    H_m(i,B)=−J_(m,i,B),
    H_m(i,B∪{i})=J_(m,i,B),       H_m(i,{i})=0.            (8)

These formulas are compatible because each owner's seven pairs are
disjoint. The non-C contribution to each gain row is a difference of two
outcome point masses on A∪L. Its ℓ¹ norm is at most 2(A+L). Consequently

    ||G_m−H_m||₁ ≤ 2D_m.                                (9)

After finite-dimensional subsequence extraction, let r_m→r*, J_m→J*,
G_m→G*. The source supplies G*∈N_cube(r*) and r*·G*=Ω>0.
Equation (9) gives G*=H*. Coordinate complementary slackness now yields:

    J*_(i,B)>0 ⇒ r*_i(B)=−1 and r*_i(B∪{i})=1;
    J*_(i,B)<0 ⇒ r*_i(B)=1 and r*_i(B∪{i})=−1.             (10)

Moreover Ω=2Σ_(i,B)|J*_(i,B)|, so some such pair is present. Every
nonzero limiting net tie flow has the maximum positive own-payoff
difference in its direction. Precisely those pairs forbid (7).

This check does not show a new inconsistency. It says that complementary
slackness supports a saturated joining/withdrawal incentive, not that it
reverses its sign. Nor does J* identify one source's gradient: it is a
net flow after the full tuple and tester averaging. Selecting an actual
response contributing to it gives an existing legal profitable response,
but does not control the other owners' full caps after a joint update.
The reversal line stops here; no conditional interior-case producer is
being substituted for the global problem.

## 4. Why averaging is not already a joint timing repair

There is also no reward-independent physical outcome transformation
implementing P on all payoff coordinates. For a fixed coalition S, owner
i∈S with |S|≥2 would need the outcome distribution assigning half its mass
to S and half to S\{i}. An outsider j would instead need half its mass on
S and half on S∪{j}. For example S={0,1}, i=0, j=2 requires two different
distributions. One actual terminal outcome has a single distribution,
shared by all payoff observers. Taking indicator reward coordinates makes
the incompatibility exact. This only rules out that particular universal
physical interpretation; it does not rule out reward-dependent repairs.

Similarly, a player cannot withdraw only on the event that someone else
quits simultaneously: the decision at that date is simultaneous and the
opponents' private clocks are not observed. A legal random delay also
changes histories on which the player was the unique first quitter, and
changes untouched owners' counterfactual payoffs. Those terms cannot be
removed by citing (2). Arbitrary timing refinements must also retain their
new inter-date, after-support, and Never responses.

## 5. Source comparison and stopping point

The named declarations inspected for the probability semantics were
`quittingFiniteCalendarCoalitionMass`, `quittingFiniteCalendarRawPayoff`, and
`quittingFiniteCalendarNeverMass` in
`UniformEquilibrium/Quitting/Paths/FiniteCalendarRawPayoff.lean`, and
`sSup_range_quittingTerminalPayoff_update_eq_pureTime` in
`UniformEquilibrium/Quitting/Cycles/BehaviorPureTimeExtremality.lean`.
No Lean build was run. The outer certificate and its precise optimizing
quantifiers are the reviewed source linked in Section 1, not a new claim
that arbitrary law mixtures have normal gradients.

The bounded comparison also read HILBERT's
[collision-subsidy test](CODEX_HILBERT__COLLISION_SUBSIDY_POLYNOMIAL_TRANSPORT_TEST.md),
ROOT's
[collision anti-diffusion and transfer note](CODEX_ROOT__NONSINGLETON_COLLISION_ANTIDIFFUSION_LINEAR_TRANSFER.md),
and HILBERT's
[full coordinate-repair trap](CODEX_HILBERT__FULL_EXPLOITABILITY_COORDINATE_REPAIR_TRAP.md).
The subsidy note loses its tolerance before reaching its sure-root target;
the collision transfer does not close repeated debt transfer; the repair
trap is explicitly not a true positive global minimum. None is used here
as a substitute for the global source. No new literature theorem is used.

The exact blocked operation is now recorded: common collision-pair
flattening removes the relevant weighted gain with the allowed negative
normal sign; amplification is prohibited on the very saturated pairs
selected by complementary slackness. A next attempt must supply a genuinely
joint, source-valid full-response comparison bypassing those pairs, or a
different common feasible table perturbation with a justified opposite
sign. Merely reselecting a favorite net-flow edge or repeating the boundary
calculation does neither. The tie arm remains unconsumed.
