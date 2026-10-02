# Dummy-priority padding and exact row perfection

External REDUCTION mathematics, preserved by CODEX_HILBERT with the
reviewed distinction from old-quitter-priority padding. Ordinary
mathematics. Original SHA-256:
`1a59b513cc8d1f127c773b72b4d1ee0d8bf3b0e23203f16e6d2f9b4cd70a35db`.
See [the source correspondence](../feedback/REDUCTION__SOURCE_CORRESPONDENCE_BY_CODEX_RENY.md).

## 1. Table and arbitrary-profile retraction

Let I be nonempty and finite. An old quitting game has terminal vectors
r(S) for nonempty S⊆I and arbitrary Never vector z. Set L_i and H_i
to the minimum and maximum of all old terminal and Never rewards, and
W=max_i(H_i−L_i). Add one player d and choose K>0. Keep the old Never
coordinates and give d Never payoff zero. If d belongs to a terminal
coalition, pay each old player H_i and pay d the amount −K. Otherwise
pay the old coalition its old vector and pay d zero.

All players use independent complete stopping laws. For any enlarged
profile (p,p_d), couple it to the old profile p using the same old clocks.
Let T be the earliest old finite stopping date, with T=Never if none, and
let A={T_d finite and T_d≤T}. Put p_A=Pr(A). The enlarged old-player
payoff differs from the old payoff only on A, where it is raised to H_i.
Consequently

    0≤Û_i−U_i≤(H_i−L_i)p_A.

The dummy has cap zero, attained by Never, and prescribed payoff −Kp_A;
its exact full debt is therefore Kp_A. For every arbitrary old-player
deviation τ_i, the same coupling gives

    U_i(τ_i,p_−i)≤Û_i(τ_i,p̂_−i).

No bound on the intervention probability after this deviation is required.
Taking full response suprema and subtracting prescribed payoffs proves

    d_i(p)≤d̂_i(p̂)+(H_i−L_i)d̂_d(p̂)/K,
    E(p)≤(1+W/K)Ê(p̂).                                (1)

Conversely adjoining dummy Never leaves every old payoff and cap unchanged,
and gives the dummy its maximal payoff zero. Thus it is an exact quiet lift.
With g=inf_actual E and ĝ=inf_actual Ê,

    g/(1+W/K)≤ĝ≤g.                                    (2)

Exact terminal Nash existence and all-accuracy terminal Nash existence are
preserved both ways. The construction is rational for rational data and
rational K. For old rewards including z in [−1,1], choosing K=1 keeps
the enlarged rewards in that box and gives ĝ≥g/3.

## 2. Actual stationary row-perfect source

Choose any α∈(0,1]. At every date let d Quit with probability α and
all old players Continue. Every restarted sequence terminates almost surely
at the dummy singleton. Its literal restarted value is (H,−K).

For an old player i, the current Quit endpoint is
(1−α)r_i({i})+αH_i≤H_i; Continue and its prescribed value both equal
H_i. For the dummy both pure endpoints and its prescribed value equal −K.
Thus every row is exact product Nash against its **actual** next restarted
value: both endpoints are at most the prescribed value, and every supported
action attains it. This is exact row perfection, not a full-strategy Nash
claim. The dummy's complete Never deviation gains K.

The survival from restart m through the rows before N is
(1−α)^(N−m). It is positive at every finite date if α<1 and tends to
zero after every restart. The same source works at every positive row
error; its only positive hazard can be arbitrarily small but fixed.

## 3. Scope and the priority convention

Consequently the universal assertion that every finite-player table with
such an exact stationary, every-restart absorbing row-perfect source has
all-accuracy terminal Nash profiles is equivalent to universal
all-accuracy terminal Nash existence. The forward implication applies the
assertion to this enlarged game and uses (1); the reverse is immediate.
This uses one additional player, not a same-cardinality hardness theorem.

The checked padding instead gives priority to a nonempty old quitting
coalition: joining by d does not change its rewards, and d is penalized
only when it quits alone first. Its intervention event is T_d<T rather
than the event T_d≤T above. Its analogous pointwise retraction and global
bounds are already in
`Quitting/Terminal/PassivePlayerPaddingExploitabilityRetraction.lean`.
The universal reverse-source equivalence is already in
`Quitting/Classification/Existence/ReverseSequentiallyPerfectAbsorbingHardness.lean`.
These tables are not definitionally identical, but the same one-sided
payoff comparison proves (1) for both.

The arbitrary-α, positive-finite-reach source on the existing old-priority
table is separately proved in
[CODEX_RENY__POSITIVE_FINITE_REACH_ROW_PERFECT_PADDING.md](CODEX_RENY__POSITIVE_FINITE_REACH_ROW_PERFECT_PADDING.md).
Neither padding supplies approximate equilibria of the old game. The
remaining reverse existence assertion is unchanged by this representation.
