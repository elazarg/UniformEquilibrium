# The reset-rank family has an exact stationary equilibrium

Identity: CODEX_FRECHET_CYCLE.

Status: complete ordinary-mathematics construction, not independently
reviewed or checked in Lean. The exact requested member a=2, β=1 is
solved, and the same elementary formula solves the entire revised
two-parameter family. This family is therefore NOT a negative candidate.
No barrier-degree search, parameter grid, or constant optimization was
performed.

The separate frozen grammar note is
`CODEX_FRECHET_CYCLE__QUADRATIC_FULL_BOX_BARRIER_RESET_RANK_TEST.md`,
SHA-256 `668368fc2ee6aa3f4a6a41342ef626bc81302e9942e9d04c1acbd403c4e35b40`.
Its general reset-rank lemma concerns arbitrary quadratic full-box
barriers. The current construction establishes that its displayed
application family has zero controller value, so that application is
not evidence for a positive gap or a need for a richer negative barrier.
The frozen note was not altered.

## 1. Fully specified game and actual strategy

Players are I={0,1,2,3}, with indices read modulo four. Parameters satisfy

    β>0,       a>max(1,β).

For singleton coalitions define

    r_i({j})=1       if i=j=0;
             0       if i=j≠0;
             a       if (i,j)=(1,0);
            −a       for every other i≠j.

For |S|≥2 set

    r_i(S)=β ε_i t_i(S)t_(i+1)(S),
    ε=(1,1,1,−1),       t_i(S)=2·1_(i∈S)−1.                 (T)

Never pays zero. The reward bound M=a is valid. The own-singleton
vector is canonical (1,0,0,0); no punishment-normality hypothesis is
needed for the construction below.

At every live date use the same independent product root

    q_0=1,
    q_1=p=(a−β)/(a+β),
    q_2=t=(a+β)/(a+3β),
    q_3=0.                                                  (Q)

Both p and t lie strictly between zero and one. Random choices by
players 1 and 2 are private and independent, at each live date and
across players. Player 0 Quits surely and player 3 always Continues.
All off-path live rows are the same q: there is no separate punishment
tail, public signal, or supplied equilibrium continuation.

Prescribed play absorbs at the first root. Define

    ρ=(1−p)(1−t)=4β²/((a+β)(a+3β)),
    g=β(a−β)/(a+3β),
    v_0=g+(1−β)ρ,
    v=(v_0,g,−β,g).                                         (V)

We prove that (Q) is exact terminal Nash against ALL complete behavioral
replacements, has actual payoff v, and v is a uniform-equilibrium payoff.

## 2. Exact full-cap formula

For a stationary product root let α_i be its opponent all-Continue
probability, Q_i its immediate-Quit payoff, and A_i the absorbing
contribution when player i Continues. If α_i<1, put

    N_i=A_i/(1−α_i).

Against the fixed stationary opponents, Quit at date n gives

    N_i(1−α_i^n)+α_i^n Q_i,

and Never gives N_i. Therefore the unrestricted complete cap is

    B_i=max(Q_i,N_i).                                       (C)

The same conclusion covers privately randomized, history-dependent
behavioral replacements, by pure-time extremality along the unique
preabsorption public history. It is not a restriction to stationary
deviations.

The inspected production declaration
`quittingBestReplyValue_stationary` in
`UniformEquilibrium/Quitting/Stationary/MinMax.lean` identifies this
full behavioral cap with `quittingStationaryUnilateralCap`.
`quittingStationaryUnilateralCap_eq_max_div` gives the displayed two
endpoints, and `quittingTerminalPayoff_update_stationary_le_cap`
bounds every complete behavioral deviation. All our α_i are below one,
so no saturated-opponent boundary convention is needed.

## 3. The exact rational member requested

At a=2, β=1, the root and prescribed payoff are

    q=(1,1/3,3/5,0),
    v=(1/5,1/5,−1,1/5).

Direct evaluation of every relevant cap gives the following table.

| Player | α_i | Q_i | A_i | N_i | Actual v_i=B_i |
|---|---|---|---|---|---|
| 0 | 4/15 | 1/5 | −19/15 | −19/11 | 1/5 |
| 1 | 0 | 1/5 | 1/5 | 1/5 | 1/5 |
| 2 | 0 | −1 | −1 | −1 | −1 |
| 3 | 0 | −1 | 1/5 | 1/5 | 1/5 |

Thus player 0 strictly prefers Quit, players 1 and 2 are exactly
indifferent and can use their specified interior hazards, and player 3
strictly prefers Continue. Equation (C) makes this an unrestricted
equilibrium certificate, not just four one-stage inequalities.

## 4. Symbolic proof for the whole family

Players 1, 2, and 3 always face a sure opponent, player 0. Their α_i=0,
so every unilateral replacement is settled by its first binary action.

For player 1, immediate Quit pays

    Q_1=β(2t−1).

If player 1 Continues, player 2's Continue leads to singleton {0},
paying a, while its Quit leads to {0,2}, paying −β. Thus

    A_1=a−(a+β)t.

The chosen t=(a+β)/(a+3β) makes Q_1=A_1=g.

For player 2, immediate Quit pays −β regardless of player 1's action.
If it Continues, the terminal coalition is {0} or {0,1}, so

    Q_2=−β,
    A_2=−a+(a+β)p.

The chosen p=(a−β)/(a+β) makes Q_2=A_2=−β.

For player 3, Quit pays −β regardless of players 1 and 2. Continue
pays −a only on singleton {0}, and β on every other prescribed
coalition. Consequently

    Q_3=−β,
    A_3=β−(a+β)ρ
       =β−4β²/(a+3β)=g>0.

Hence player 3's prescribed Never is strictly optimal.

It remains to check player 0, the only player whose deviation can
expose later live rows. Its immediate-Quit outcomes have rewards

    {0}: 1,       {0,1}: β,       {0,2}: −β,       {0,1,2}: β.

Their product expectation is

    Q_0=β−2β(1−p)t+(1−β)ρ
       =g+(1−β)ρ=v_0.

In particular Q_0>−β: all four listed rewards are at least −β,
and the positive-reward outcomes have positive probability.

If player 0 Continues until an opponent absorbs, the only terminal
coalitions are {1}, {2}, and {1,2}. Its payoffs there are respectively
−a, −a, and −β. Opponents 1 and 2 have positive hazards and hence
absorb almost surely; their all-Continue probability is ρ<1. It follows
at once that

    N_0≤−β<Q_0.

For an algebraic check, the exact quantities are

    A_0=−β(5a²−β²)/((a+β)(a+3β)),
    N_0=−β(5a²−β²)/(a²+4aβ−β²)<−β.

The last strict inequality follows from a>β>0. Equation (C) therefore
gives B_0=Q_0=v_0. Since q_0=1, prescribed absorption occurs at once
and the actual payoff is exactly (V). Every coordinate equals its
complete behavioral cap, proving exact terminal Nash. QED.

## 5. Fixed target and uniform-horizon conclusion

For the same q we have joint all-Continue mass zero and

    α_0=ρ<1,       α_1=α_2=α_3=0.

The actual vector v is a fixed point of root prescribed payoff because
q absorbs surely. The preceding proof also gives exact root Nash
against v. Consequently the inspected declaration
`isUniformEquilibriumPayoff_of_stationaryEndpointCertificate_contracts`
in `UniformEquilibrium/Quitting/Stationary/EndpointCompiler.lean`
applies to these explicit data. Its conclusion is the one fixed
uniform-equilibrium payoff v, against every behavioral deviation.

The elementary uniformity mechanism is visible directly: regardless
of player 0's replacement, the chance that both other active players
survive n dates is ρ^n; deviations by any other player still face
player 0's sure first-date exit. Thus the terminal-to-long-finite-horizon
comparison is uniform over the deviator, not merely pointwise in its
stopping law. No moving payoff target or supplied periodic tail enters.

The numeric/symbolic identities in Sections 3--4 were checked with exact
SymPy arithmetic after substituting (Q) into the eight product-root
endpoint sums. The general proof above is independent of that check.

## 6. Discovery record, source status, and stop

The bounded test first tried the full interior indifference equations
Q_i(1−α_i)=A_i at a=2, β=1, from the single initial guess (1/2)^4.
That numerical root solve failed to converge; this was not interpreted
as infeasibility. On the face q_0=1 the exact outsider equations instead
exposed q_3=0, and their two linear indifferences gave q_1=1/3,
q_2=3/5. Solving these same two displayed linear equations symbolically
gave (Q); no additional parameter probe or grid was performed.

Exact source lookup followed the stationary endpoint/face entries of
`docs/TOOLKIT.md` to the named cap and compiler declarations in
Sections 2 and 5. No Lean implementation, build, or audit was performed
for this new parameterized certificate. Its status is ordinary proved
mathematics with an exact existing production consumer, not a newly
Lean-checked family theorem.

The concrete negative-candidate check is complete and positive: this
whole family has a fixed uniform-equilibrium payoff, so it cannot
support ANY positive all-behavior barrier. The separate reset-rank
lemma remains a valid general statement about full-box quadratic
functions; its application here carries no negative-route evidence.
The task stops at this actual strategy construction, with no export,
commit, barrier amendment, or further family expansion.
