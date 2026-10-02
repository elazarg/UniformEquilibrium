# R: padding variants and exact SUM-debt infimum preservation

Recorder and independent checker: `CODEX_FRECHET_CYCLE`.

Status: preservation of valid ordinary mathematics from the first two
responses in `gpt/R.md`, reviewed in
`feedback/R__BY_CODEX_FRECHET_CYCLE.md`. Input SHA:
`bc35abd855ba89f228c50079d08524d44b8964d8e893257e71062c7c6fe66593`.
The main universal hardness equivalence and MAX-gap retraction are already
in production; this note retains only the construction distinctions and
the SUM-infimum corollary. No new research, Lean, or export claim.

## 1. Two different collision rules

Let an arbitrary finite nonempty quitting game have players I, terminal
rewards r(S), Never payoff z, and independent complete stopping laws.
Every unilateral behavioral replacement is allowed. Choose M,K>0 with
|r_i(S)|,|z_i|≤M. Add a player d whose Never payoff is zero.

The USER'S dummy-priority padding is

    r̂(S)=(r(S),0)                       if d∉S;
    r̂(S)=(M·1,−K)                       if d∈S;
    ẑ=(z,0).

Thus a collision containing d overrides all original rewards and penalizes
d. By contrast, the existing PRODUCTION padding gives old players priority.
Writing u_i=max({z_i}∪{r_i(S):S nonempty}), its rewards are

    r̄(S)=(r(S),0)                       for old-only S;
    r̄(S∪{d})=(r(S),0)                   for nonempty old S;
    r̄({d})=(u,−K),                      z̄=(z,0).

The relevant exceptional event is therefore any absorption containing d
for r̂, but dummy-only absorption for r̄. Both constructions preserve the
original game exactly when d uses Never. Neither construction supplies
an equilibrium of an arbitrary original game.

## 2. Exact geometric sources and the genuinely different mixed variant

In either padding let only d Quit, with one fixed probability h∈(0,1)
at every date. Every restarted tail has payoff (M·1,−K) for r̂ or
(u,−K) for r̄, and survival over t dates is (1−h)^t. For d, Quit and
Continue both pay −K. In r̂ an old player's Quit endpoint is
hM+(1−h)s_i≤M; in r̄ it is s_i≤u_i. Continue pays the respective
upper coordinate. Hence every row is exactly playerwise 0-perfect.
All finite live histories have positive probability and every restart
terminates geometrically. This is an elementary modification of the
already checked production sure-dummy source, not new main hardness.

There is a narrower source restriction supported by r̂. Put n=|I| and,
for 0<t<1/2, prescribe the stationary product root

    q_d=1−t,       q_i=t for every old i,
    b=(1−t)^n.

All players use both actions. Joint Continue is tb<1/2, so prescribed
termination is uniformly geometric across this family. The actual dummy
payoff and endpoints are

    U_d=−K(1−t)/(1−tb),
    Q_d=−K,      C_d=bU_d,
    C_d−Q_d=K(1−b)/(1−tb)≤2Knt.

For each old player and either pure root action, d Quits immediately with
probability 1−t and gives that player M. Conditional on d Continuing,
the terminal or actual continuation payoff belongs to [−M,M]. Hence

    Q_i,C_i∈[M−2Mt,M].

The prescribed value is their convex combination. Every pure endpoint is
therefore within ε_t=2t max(M,Kn) of its prescribed value. These actual
stationary sources are playerwise ε_t-perfect at every row, with ε_t→0.

Deleting any one player leaves an absorbing stationary opponent clock for
each FIXED t. Thus every unilateral behavioral deviation still terminates
almost surely. This is NOT uniform deleted-clock contraction as t→0:
when d is deleted, the opponents' Continue factor b tends to one.
Indeed d's full cap is zero by Never, and its actual full debt is

    d_d=K(1−t)/(1−tb)→K.

Thus even these fully mixed, all-deviation-terminating supplied sources
need not approach equilibrium. They do not refute existence of some other
approximate equilibrium.

The proof does not transfer unchanged to r̄. There an old player's Quit
endpoint tends to s_i, while Continue tends to u_i. If s_i<u_i, positive
Quit support has a nonvanishing loss. The dummy-priority collision rule
is doing real work in the mixed-source variant.

## 3. Unrestricted projection and exact SUM-infimum equality

For either padded game, take ANY actual profile p̂ and project it to its
old-player laws p. Let α be the appropriate exceptional probability from
Section 1. Player d always has full cap zero, since all its rewards are
nonpositive and Never guarantees zero. Its debt is exactly Kα.

Couple the same complete old stopping laws in both games. Outside the
exceptional event payoffs agree. On that event the padded payoff for each
old player replaces its original realized payoff by an upper bound. Hence

    0≤U_i(p̂)−U_i(p)≤w_i α,
    B_i(p)≤B_i(p̂),
    d_i(p)≤d_i(p̂)+w_i α.                         (PROJ)

For dummy-priority padding one may take w_i=2M. For production padding
one may take the sharper

    w_i=u_i−l_i,
    l_i=min({z_i}∪{r_i(S):S nonempty}).

The cap inequality uses the same monotone coupling separately under EVERY
old-player replacement. The exceptional probability under a deviation may
change; no bound by the prescribed α is required for that cap comparison.
The prescribed payoff estimate is the only place prescribed α is used.
Thus (PROJ) covers arbitrary finite dates, Never, nonstationary laws and
collisions, without response attainment.

Let D(p)=Σ_i d_i(p), and D_* its infimum over all actual independent
product stopping-law profiles. Summing (PROJ) gives

    D_old(p)≤Σ_(old i)d_i(p̂)+αΣ_i w_i.

Consequently K≥Σ_i w_i implies D_old(p)≤D_padded(p̂) for EVERY padded
profile. Conversely, extending any old profile with d Never preserves
every old prescribed payoff and full cap, and gives d zero debt. Hence

    K≥Σ_i w_i  ⇒  D_*(padded)=D_*(old).           (SUM)

This is equality of infima; neither minimizing profiles nor best responses
need attain their values. In the user's symmetric bound, K≥2M|I|
suffices. It is a direct consequence of the existing padding coupling,
not a new method for deciding the equilibrium conjecture.

## 4. Exact source homes and limits

Production collision formulas, arbitrary-Never normalization, the exact
stationary source and unrestricted MAX projection are in
`UniformEquilibrium/Quitting/Classification/Existence/ReverseSequentiallyPerfectAbsorbingHardness.lean`,
under `QuittingPayoffTable.oneDummyPadding`, its
`oneDummyPadding_terminal_*` case declarations,
`oneDummyPadding_has_stationaryExactEveryRestartSource`, and
`oneDummyPadding_project_exploitability_le`.

The already checked universal equivalence is
`universalStationaryExactEveryRestartSource_iff_approximateExistence`;
its hard direction adds exactly one player. The checked MAX-infimum
comparisons are in
`Quitting/Terminal/PassivePlayerPaddingExploitabilityRetraction.lean` as
`retractionFactor_mul_quittingTerminalExploitabilityInf_le_padding` and
`quittingTerminalExploitabilityInf_padding_le`.

No named SUM equality was found in the narrowly inspected padding/existence
sources. Formula (SUM) is preserved as ordinary mathematics. The fully
mixed-source restriction is likewise an ordinary variant; neither changes
the already-formalized main hardness equivalence.

These padded sources have an abnormal player: P_d=0>s_d=−K. The generic
normal-source compiler cannot be applied to them as though all players
were punishment-normal. In four players, existing same-table normality
under a no-UE assumption already settles reverse S.3; that does not supply
S.3 for arbitrary four-player games. No contradiction to those results or
new positive-gap example is asserted here.
