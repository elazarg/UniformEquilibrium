# Ordered positive premiums: negative premiums need no restriction

Author: CODEX_HILBERT. The premise weakening was proposed by ROOT;
CODEX_RENY independently identified the same semantic extension.

Status: complete ordinary-mathematical contribution, frozen for a fresh
independent final review. This changes the raw hypothesis of the
Solan–Vieille adapter, not the separate exact lower-boundary theorem.
No prior frozen note, export, or Lean source is modified.

## 1. Weaker table theorem

Let I be finite and nonempty, let r_i(S) be arbitrary finite real rewards
on nonempty quitting coalitions, let Never pay zero, and put
s_i=r_i({i})≥0. Assume

    For every nonempty A⊆I there is i∈A such that
        r_i(S)≤s_i for every i∈S⊆A.                           (WSP)

Then there are terminal approximate Nash profiles at every positive error,
against every unilateral behavioral deviation. Profiles can be periodic
from time zero with the same full error bound at every suffix. Hence there
is one fixed uniform-equilibrium payoff of the original table.

No lower bound r_i(S)≥s_i is imposed. In particular, all negative own
premiums and all passive rewards are arbitrary. No punishment value or
punishment-normality premise is needed for this proof.

## 2. Equivalent positive-premium ordering

Condition (WSP) holds exactly when there is an ordering i₁,…,i_n such that

    i_m∈S and r_(i_m)(S)>s_(i_m)
        ⇒ S contains some i_ℓ with ℓ<m.                      (ORD+)

To construct the order, apply (WSP) to the remaining players and remove
the selected one. A coalition paying that player a strict premium cannot
be wholly contained in the then-remaining set, so it contains an earlier
player. Conversely, choose the earliest member of any nonempty A. A
coalition S⊆A containing it cannot pay a positive premium, because that
would require an earlier member in A. Therefore its reward is at most
its singleton value. Neither direction uses nonnegative own premiums.

## 3. Exact change to the root-choice argument

First normalize own singleton levels to 1. At any continuation v, choose
an exact product Nash root q in the finite one-shot game. If its active
set A={i:q_i>0} is nonempty, choose i from (WSP). Every possible coalition
in i's Quit endpoint is contained in A, so

    Q_i(q)≤1.

Since Quit is supported, its prescribed payoff equals Q_i(q). This is
exactly the active-low-payoff alternative in Solan–Vieille Proposition 2.2;
equality to 1 was never required by that proposition.

On W={v∈[−R,R]^I : some v_i≤1}, with R≥1 bounding all rewards, the
all-Continue alternative is handled as before. Exact root Nash gives
v_j≥1 for every j, so a coordinate selected by membership in W equals 1.
That player is indifferent and may be made to Quit with small probability.

For an active selected i, boost its hazard to q_i+δ(1−q_i). There are only
two cases: if 0<q_i<1, its two endpoints are equal by exact Nash, and its
payoff stays Q_i≤1; if q_i=1, the root is unchanged. Thus the boosted
successor still belongs to W and its absorption is at least δ. No new
Quit action is introduced at an inactive player in this case. In the
all-Continue case the newly introduced Quit action is exactly indifferent.

Other players retain their original supports. Their individual pure-action
payoffs change by at most 2Rδ, so support regret is at most 4Rδ. This
estimate uses bounded rewards and the common source continuation only;
it is unaffected by the signs of the own premiums.

The remaining finite-mesh argument is literally unchanged: for requested
row error τ choose δ=min(1/2,τ/(8R)) and mesh radius ζ=δτ/4. A finite
representative map has a cycle; reverse it to obtain periodic product rows
with absorption at least δ. Actual suffix payoffs differ from annotations
by at most ζ/δ, so support regret against actual suffix payoffs is at most
4Rδ+2ζ/δ≤τ. Every suffix terminates. The old unit-only full-response
extraction then gives the desired terminal error, including Never and
arbitrarily late deviations. Per-row errors alone are not being summed to
claim that conclusion.

## 4. Original zero-Never semantics and final scope

For an original requested terminal error ε>0 set t=ε/4, η=ε/2, and

    d_i=s_i+t>0,       r̂_i(S)=[r_i(S)+t]/d_i.

This preserves (WSP), gives unit own singletons, and leaves Never zero.
Apply the normalized result with full error η/max_i d_i. Undoing positive
scales gives error at most η for r+t. Every actual profile or deviation
has payoff changed by at most t under the terminal-only addition, since
the change equals t times its absorption probability. Thus original full
regret is at most η+2t=ε. This holds at every suffix. The terminal-all-errors
fixed-payoff consumer finishes; neither periods nor normalized tables need
be common across accuracies.

All exact downstream statements, original-paper citations, and the full
finite-mesh proof are preserved in
[the frozen adapter](CODEX_HILBERT__FINITE_PREMIUM_PEELING_SOLAN_VIEILLE_ADAPTER.md),
SHA-256 `48933b7ca0a0e321c8dfd38253f668d8e00f751b514d0a7282d5619560f68084`.
The only changed input and proof step are spelled out above. In particular,
production's `quittingPeriodicPerfectSequenceSubgameExtraction_of_soloExitPreference`
requires unit solos only. The generic row producer must still be attached
to the new table condition rather than supplied as an output field.

The expanded theorem does NOT assert P=s or that exact root successors
lie coordinatewise above s. Nor does it extend the equivalence with a common
lower boundary or the C¹ minimum argument: those separate claims retain
their nonnegative-own-premium premise. The expanded existence route needs
only the upper condition at one active receiver, precisely as in the old
conditional theorem.

Next requested check: independently review this weakening together with the
full adapter in the final assembled theorem; do not count this contributor's
verification as that independent review.
