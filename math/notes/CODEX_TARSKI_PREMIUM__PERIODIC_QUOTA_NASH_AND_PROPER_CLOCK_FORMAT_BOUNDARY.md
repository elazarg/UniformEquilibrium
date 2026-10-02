# Periodic quota Nash and the proper-clock format boundary

Identity: CODEX_TARSKI_PREMIUM.

Status: complete ordinary-mathematics checkpoint; no Lean implementation or
export proposed. Exact constrained Nash profiles exist and have the explicit
full-debt formula below. The intended universal selection program is false:
a solved canonical four-player table excludes its entire output format,
uniformly over every period and every positive quota vector. The obstruction
is the probability-scope extension of
[NOETHER's proper-support example](CODEX_NOETHER_SUPPORT__PROPER_SUPPORT_FULL_ACTIVITY_STATIONARY_OBSTRUCTION.md),
not a new independent obstruction mechanism.

## 1. The proposed producer and exact quantifiers

Fix a finite player set with at least two players and a real reward table r
on nonempty coalitions. All-Never and preabsorption pay zero. Players use
independent private behavioral randomization; a deviation can replace the
whole stopping law on the nonnegative integers together with Never. Write
U_i, B_i, d_i=B_i−U_i and E=max_i d_i for actual prescribed payoffs, full
response caps, and terminal debts.

For a period N≥1 and quotas τ_i∈(0,1], player i chooses one cycle law

    a_it≥0 (0≤t<N),  z_i≥0,  Σ_t a_it+z_i=1,  m_i=1−z_i≥τ_i.

Conditional on its own survival, the player independently repeats this law
each cycle. Thus its actual stopping probabilities are

    Pr(T_i=kN+t)=z_i^k a_it,    Pr(T_i=Never)=0.

The cycle-Continue probability z_i is NOT actual Never mass. Every output
clock is proper, even if the quota is arbitrarily small. Zero-survival
off-path hazards may be filled arbitrarily while retaining periodicity.

The attempted universal claim was: for every canonical four-player reward
table and ε>0, select N, positive quotas, and an exact Nash equilibrium of
this constrained cycle-law game whose ORIGINAL full exploitability is below
ε. Section 3 refutes even the claim with “exact Nash equilibrium” omitted.

## 2. Valid producer and full-debt identity

Fix the opponents' cycle laws. Put D_i=∏_{j≠i}z_j<1. Let H_i be the
unconditional reward contribution during the first cycle when i Continues
throughout it, and let K_it be its actual payoff from pure Quit at date t in
that first cycle. Define

    K_i=max_{t<N} K_it,    W_i=H_i/(1−D_i).

Here W_i is the FULL periodic Never payoff. A pure Quit at date kN+t has
payoff W_i+D_i^k(K_it−W_i), so averaging arbitrary stopping laws gives

    B_i=max(K_i,W_i).

Conditioning on the first cycle and its joint survival gives the actual
payoff identity

    U_i = [Σ_t a_it K_it+z_i H_i]/[1−z_i D_i].

Its denominator is positive. At any best reply all positive finite atoms
are supported on maximizers of K_it. For a fixed finite mass m its best
payoff is therefore

    f_i(m)=[mK_i+(1−m)(1−D_i)W_i]/[1−D_i+mD_i].

Its derivative has the sign of K_i−W_i, since its numerator after clearing
the positive squared denominator is (1−D_i)(K_i−W_i). Consequently a
best reply has m=1 if K_i>W_i, m=τ_i if K_i<W_i, and any allowed mass if
they are equal. The maximizing-date simplex with the indicated mass choice
is nonempty, compact and convex.

The product of all cycle-law domains is compact and convex. Payoffs are
continuous, since 1−∏_j z_j≥1−∏_j(1−τ_j)>0 uniformly. The best-reply
correspondence is upper hemicontinuous by the maximum theorem, with the
nonempty compact convex values just described. Kakutani's fixed-point
theorem therefore gives an actual exact Nash profile of the constrained
cycle-law game for every N and positive quota vector. This is ordinary
finite-dimensional mathematics, not a claimed repository declaration.

At every such constrained equilibrium its ORIGINAL full debt is exactly

    d_i = τ_i (W_i−K_i)₊ / [1−D_i+τ_i D_i].

In particular, nonbinding quota implies zero full debt. Small τ_i alone
does not give a small ratio: the opponents' absorption probability 1−D_i
can vanish on the same or a faster scale.

Boundary warning: if zero quotas are newly allowed, D_i=1 means all the
opponents actually use Never. Then H_i=0 and the displayed ratio defining
W_i is invalid. The literal Never value is zero and B_i=max(0,r_i({i})).
If i has positive cycle finite mass, U_i=r_i({i}); if it has zero mass,
U_i=0. These distinct boundary values cannot be obtained by blindly
substituting into the positive-denominator formulas or the fixed-point
argument. The original producer avoided this boundary by imposing all
quotas strictly positive; that restriction is precisely fatal below.

For any supplied periodic output, finite-law censorship is harmless once
the actual debt is known: after K cycles its i-th finite tail mass is z_i^K.
Replacing these finite tails by Never changes E by at most
4MΣ_i z_i^K when |r_i(S)|≤M. Coupling only the opponents gives the response
bound uniformly over ALL deviations. This compiler cannot turn the debt
floor below into a vanishing debt merely by accurate censorship.

## 3. Canonical whole-format obstruction

Take I={0,1,2,3}. On a proper nonempty coalition S define

    r_0(S)=1 if 0∈S, and 3 otherwise;
    r_j(S)=0 if j∈S, and 2 otherwise, for j=1,2,3.

At the grand coalition put r(I)=(2,1,1,1); Never pays zero. The own singleton
vector is literally (1,0,0,0). This is a directly specified canonical table;
no claim about arbitrary terminal-coordinate translations is used.

Suppose a profile has, for every player i, an opponent quitting at some
finite time almost surely. Never then receives 3 for player 0 and 2 for
each other player. These are also the largest corresponding reward
coordinates. Hence its full caps are exactly (3,2,2,2).

The prescribed profile absorbs almost surely. At a proper coalition of
size k its total reward is 9−2k≤7, and at the grand coalition the total
is 5. It follows that

    Σ_i U_i≤7,    Σ_i d_i≥9−7=2,    E≥1/2.

The hypothesis holds whenever at least two individual clocks are proper;
in particular it holds for EVERY positive-quota periodic output, with no
restriction on N, quotas, phases, Nash selection, or relative rates.

Nevertheless player 0 Quit at date zero and the other three Never form an
exact full Nash equilibrium, with payoff (1,2,2,2). The pivot's cap against
all-Never opponents is 1, and the other players already get their maximal
reward 2. This is also an exact uniform-payoff profile: absorption is at
date zero and those same bounds hold at every finite horizon. Thus the
format cannot approximate even this finite-menu exact source in full
exploitability. There is no positive global minimum for this game.

The calculation extends NOETHER's stationary example to the actual
probability hypothesis its proof uses. The canonical table equals that
example minus one in each nonpivot terminal coordinate, but the proof here
checks the resulting table directly, including its unchanged zero Never.
An integer enumeration checked all 15 coalition rewards, their coordinate
upper bounds, and the exact maximum total reward 7; the all-behavior proof
is the argument above, not the enumeration.

## 4. Source comparison and stopped implication

The exact unrestricted periodic window is already represented by
`sSup_range_quittingTerminalPayoff_update_eq_periodicWindow` and
`sSup_range_quittingRootSequencePureTimeTerminalValue_eq_finiteWindow`
in `UniformEquilibrium/Quitting/Cycles/PeriodicWindowEvaluation.lean`.
Their actual periodicity hypotheses and full behavioral supremum were read.
The supplied-format distinction and boundary branches also appear in
[the fixed-format certificate](CODEX_HILBERT__FIXED_PERIODIC_FORMAT_ALL_ACCURACY_CERTIFICATE.md).

[SPINOZA's phase-flat obstruction](CODEX_SPINOZA__GROWING_PERIOD_HAZARD_CLOCK_AND_REPLICATOR_BOUNDARY.md)
assumes common-temperature logit roots and period times temperature tending
to zero. It does not directly refute this exact quota-Nash construction.
The present format check is instead decisive before such equilibrium
selection questions arise: increasing the period cannot remove mandatory
properness of every clock.

Retired implication: existence of exact quota Nash for every period and
every positive quota does NOT permit selecting original debts tending to
zero. No gate or further universal quota-selector work is proposed.

Next mathematical question must allow exact Never mass and simultaneous
changes of all laws. Allowing zero quotas, freezing an inactive face, or
adding permanent private Never choices changes the producer and needs its
own source-existence and complete outsider-cap proof; none is asserted here.
