# Proper-support balance does not consume a full-support exit by stationarity

Identity: CODEX_NOETHER_SUPPORT.

Status: bounded mechanism obstruction, complete ordinary mathematics.
The example satisfies every proper-support LP and has exact full-support
root exits from the classical low-payoff region. Nevertheless every
fully active stationary profile has a fixed positive unrestricted regret.
The same table has exact singleton equilibria, so this does not refute
the proposed proper-support table class or uniform-equilibrium existence.
No Lean implementation or export is proposed.

## Exact table and question

Let I have n≥2 players. Own singleton rewards are all one. At each
nonempty proper coalition S⊊I, set

r_i(S)=1 if i∈S, and r_i(S)=3 if i∉S.

At the full coalition set r_i(I)=2 for every i. Never and preabsorption
pay zero. Strategies use independent private behavioral randomization;
one deviator may replace its entire strategy, including Never.

Every nonempty proper A satisfies the supportwise weighted-premium LP:
for every nonempty S⊆A, every participant premium r_i(S)−1 is zero.
Any nonnegative normalized weight vector on A works. The full-support
LP fails, since its grand-coalition inequality would be
Σ_i w_i(2−1)=1≤0.

Tested mechanism: obtain a full-support exact one-stage root with output
outside W={v∈[−3,3]^I : min_i v_i≤1}, then consume that exit by repeating
the root or repairing it within fully active stationary profiles.

## An exact full-support exit

Use the same hazard q∈(0,1) for every player. Put
β=(1−q)^(n−1), γ=q^(n−1), and v_i=3+(γ−2)/β.
Against the opponents' root probabilities,

Quit payoff = 1+γ,
Continue payoff = 3(1−β)+βv_i = 1+γ.

Thus every player is indifferent, the root is exact mixed Nash against
v, every player is active, and its output is (1+γ,…,1+γ), strictly outside
W. This is a literal product root, not a stationary fixed point.

For q=1/(2n), Bernoulli's inequality gives β>1/2. Therefore v_i>−1.
Also γ≤q≤1−β, which implies v_i≤1. Hence this is an exact exit from
inside the specified reward cube for every n≥2.

The smallest example is n=2, q=1/2, v=(0,0). Both endpoints equal 3/2.
At n=4 take q=1/8: β=343/512, γ=1/512, v_i=6/343, and both endpoints
equal 513/512. All numbers are exact and all proper-support constraints
continue to hold.

## Every fully active stationary repair has positive regret

Now allow any stationary hazards q_i>0, not necessarily equal. Against
the fixed opponents, Never makes each player receive exactly three:
some opponent quits almost surely, and every coalition excluding the
player pays that player three. Since no reward coordinate exceeds three,
its complete behavioral cap is exactly three.

At a proper terminal coalition of size k≥1, total reward is 3n−2k≤3n−2.
At the full coalition total reward is 2n≤3n−2. The prescribed stationary
profile absorbs almost surely, so

Σ_i U_i≤3n−2,       Σ_i(B_i−U_i)≥2.

Consequently some player's full behavioral regret is at least 2/n.
In particular it is at least 1/2 for four players. This excludes every
vanishing-error repair that remains both stationary and fully active;
it is stronger than a failure of merely repeating the displayed root.

For the two-player half-hazard root, the prescribed stationary payoff
is (2,2), while each Never deviation obtains three. Its exact regret
is one per player, despite zero one-stage regret against v=(0,0).

## The boundary repair exists, and the table is solved

Choose one player to Quit at date zero and let everyone else use Never.
The quitter gets one and cannot improve against all-Never opponents.
Every other player gets three, the largest possible reward coordinate.
This is exact terminal Nash against complete behavioral deviations.

The distinction is therefore exact: proper-support balance does not
convert a fully active root exit into a stationary equilibrium while
preserving full activity. Moving to a face where some hazard is exactly
zero may be essential. The cap of the sole quitter then drops from the
interior Never value three to its singleton cap one, so continuous
stationary-regret transport across this change is also unavailable.
No assertion is made that every proper-support table admits this repair.

## Narrow source and no-go audit

The source route used `docs/TOOLKIT.md` and the previously inspected
`quittingPeriodicPerfectSequenceSubgameExtraction_of_soloExitPreference`
in `UniformEquilibrium/Quitting/Classification/Existence/PerfectSequenceExtraction.lean`.
That consumer requires perfection against actual next-tail payoffs;
the supplied exit root does not meet that hypothesis after repetition.

Further exact declarations inspected:

- `quittingContinuationBestResponseValue_stationary_eq_max_quitNow_never`
  (`UniformEquilibrium/Quitting/Stationary/CompleteBehavioralCap.lean`).
- `quittingStationaryFullRateUnilateralCap` and its opponent-saturated
  boundary clause (`UniformEquilibrium/Quitting/Stationary/FullRateStationaryVerifier.lean`).
- `quittingStationaryEndpointBounds_of_fixedPoint_rootNash`
  (`UniformEquilibrium/Quitting/Stationary/EndpointCompiler.lean`), whose
  stationary fixed-point hypothesis cannot be dropped here.

A narrow full-support/low-payoff search also found
`CODEX_MINER__AKRS_POSITIVE_ENDPOINT_FULL_SUPPORT_STATIONARY_NOGO.md`.
Its negative-singleton S.2 obstruction has a full-support stationary
equilibrium; it does not establish the present proper-support statement.
No broad code or literature survey was undertaken.

This stationary mechanism is stopped. The broader proper-support
existence claim remains unproved here. Next possible check: any proposed
consumer of a genuine full-support exit must explain its change of
support or use a different, actual nonstationary construction.
