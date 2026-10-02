# Candidate C nonsingleton fibre has a uniform-equilibrium payoff

Authors: `CODEX_NEGATIVE_CERTIFICATE`  
Independent review 1:
[`CODEX_SPINOZA`](../feedback/CODEX_NEGATIVE_CERTIFICATE__CANDIDATE_C_TWO_SCALE_SINGLETON_FIBER__BY_CODEX_SPINOZA.md),
PASS with no unresolved objection  
Independent review 2 / explicit falsification review:
[`CODEX_SNELL`](../feedback/CODEX_NEGATIVE_CERTIFICATE__CANDIDATE_C_NONSINGLETON_FIBER_UNIFORM_PAYOFF__BY_CODEX_SNELL.md),
PASS with no unresolved objection

## Exact statement

Let the player set be `I={0,1,2,3}`.  A finite quitting game has one
nonabsorbing state.  At each date each player independently chooses Continue
or Quit according to a behavioral strategy; the first date at which at least
one player Quits absorbs the game and pays `r_i(S)` to player `i`, where `S`
is that date's nonempty quitting coalition.  If nobody ever Quits, terminal
payoff is zero.  Before absorption the public history is just the number of
past all-Continue dates, so a unilateral behavioral replacement is an
arbitrary, possibly randomized and time-dependent stopping hazard, including
Never and hazards supported at arbitrarily late dates.

Assume the four singleton reward rows are exactly

```text
r({0}) = A = (1,   -3/4,  0,    1/2),
r({1}) = B = (1,   -1/2,  0,   -1/4),
r({2})     = (0,    1,   -1,    0),
r({3})     = (1/4,  1/2,  1/4, -1/4).
```

There is no assumption on any reward coordinate at a coalition of size at
least two.  Equivalently, 16 of the `15*4=60` coordinates are fixed and the
remaining 44 coordinates are arbitrary real numbers.

Then

```text
B = (1,-1/2,0,-1/4)
```

is a uniform-equilibrium payoff.  Explicitly, for every `epsilon>0` there
are one behavioral profile `sigma_epsilon` and one integer `N_epsilon` such
that, simultaneously for every horizon `N>=N_epsilon`,

1. `sigma_epsilon` is an `epsilon`-Nash equilibrium for the `N`-stage average
   payoff against every unilateral behavioral replacement; and
2. for every player `i`, the `N`-stage average payoff of
   `sigma_epsilon` differs from `B_i` by at most `epsilon`.

In particular, every game in this 44-dimensional affine fibre has terminal
exploitability infimum zero and cannot be a positive-gap Fin4 counterexample.

## Conjecture-facing change

The motivating exact quarter-grid table is `CANDIDATE_C_ROWS` in
`experiments/codex_riemann_inert_perturbation_search.py`.  It survived the
known persistent-base and ordered two-date exact exclusion chambers and had
a positive `1/4` pure-boundary toggle floor.  Before this theorem its best
recorded all-behavior result was only one finite-clock upper witness.

The theorem removes that table and, more strongly, its entire 44-coordinate
nonsingleton fibre from the Fin4 negative-certificate search.  It does not
settle games with a different singleton matrix.

## Definitions and assumptions

For the fixed reward table put

```text
M = max_{nonempty S subset I, i in I} |r_i(S)|,
D = 2M.
```

The singleton data imply `M>=1`.  Therefore every collision-minus-solo
difference obeys

```text
r_i({i,j})-r_i({i}) <= D.
```

For `0<p<1` and a positive integer `m`, define the equal-survival
micro-hazard

```text
h_m(p) = 1-(1-p)^(1/m).
```

It lies in `(0,1)`, `m` consecutive copies have total survival `1-p`, and
for fixed `p` it tends to zero as `m` tends to infinity.

Terminal `e`-Nash means that for the infinite-horizon terminal payoff, every
player and every unilateral behavioral replacement gains at most `e` over
the prescribed profile.  This is the unrestricted strategy class described
in the exact statement, not a finite deviation menu or bounded controller
class.

## Proof

### 1. Exact two-block coarse cycle

Fix `0<delta<1`.  Use owner 0 with total block hazard `delta`, followed by
owner 1 with total block hazard `1/2`.  Let `x` and `y` be the values at the
starts of those blocks.  The cyclic Bellman equations are

```text
x = delta A + (1-delta)y,
y = (1/2)B + (1/2)x.
```

Writing `d=1+delta`, their unique solution is

```text
x = (2delta A + (1-delta)B)/d,
y = (B + delta A)/d,
```

or coordinatewise

```text
x = (1,
     -1/2 - delta/(2d),
      0,
     -1/4 + 3delta/(2d)),

y = (1,
     -1/2 - delta/(4d),
      0,
     -1/4 + 3delta/(4d)).
```

Consequently

```text
||y-B||_infinity = 3delta/(4d),
eta_delta         = delta/(2d)
```

is the largest deficit of either coarse value below any player's own
singleton payoff.  The only such deficit is player 1's: its value is below
`r_1({1})=-1/2`, with the maximum deficit at `x`.  Player 0's coordinate is
identically its own singleton payoff `1`; player 2's coarse value `0` is
above its own singleton payoff `-1`; and player 3's values are at least its
own singleton payoff `-1/4`.

### 2. Exact mesh and policy value

Subdivide both blocks into `m` microphases.  Put

```text
a_0 = (1-delta)^(1/m),  h_0=1-a_0,
a_1 = (1/2)^(1/m),      h_1=1-a_1.
```

At microphase `k=0,...,m-1` of block `j`, only owner `j` mixes: it Quits
with probability `h_j`; all other players Continue.  Repeat the resulting
`2m` phases forever.  Start at microphase zero of owner 1's block.

Define the phase values

```text
V_(0,k) = A + a_0^(-k)(x-A),
V_(1,k) = B + a_1^(-k)(y-B).
```

They satisfy the exact one-step equations

```text
V_(j,k) = h_j r({j}) + (1-h_j)V_(j,k+1).
```

The block endpoints close exactly:

```text
V_(0,0)=x,  V_(0,m)=y,
V_(1,0)=y,  V_(1,m)=x.
```

Indeed `a_0^m=1-delta` and `x-A=(1-delta)(y-A)`; similarly
`a_1^m=1/2` and `y-B=(1/2)(x-B)`.

Every interpolated coordinate lies between its two coarse endpoints.  Thus
at every phase

```text
V_phase(i) >= r_i({i})-eta_delta.
```

The prescribed joint survival through a full cycle is `(1-delta)/2<1`.
Therefore absorption occurs almost surely and the profile's terminal payoff
is exactly its initial phase value `y`.

### 3. One-shot Quit bound

Consider a phase owned by `j`, with hazard `h`, and a deviating player `i`.
If `i!=j`, immediate Quit yields

```text
Q_i=(1-h)r_i({i})+h r_i({i,j}).
```

Using the phase floor and the definition of `D`,

```text
Q_i-V_phase(i)
 <= eta_delta + h(r_i({i,j})-r_i({i}))
 <= eta_delta + Dh.
```

If `i=j`, immediate Quit yields its own singleton reward.  Owner 0 has no
deficit at all; owner 1's deficit is at most `eta_delta`.  Hence the same
common bound holds for every player's pure-Quit branch.

### 4. The one-sided Continue inequality

This is the only point not covered literally by the existing exact-active
singleton certificate, so it is proved directly.

For a passive player, prescribed play is pure Continue.  Its Continue branch
against the active owner's hazard is exactly the current Bellman value by the
equation in Step 2.

For owner 0, its entire block coordinate is constantly `1`; pure Continue,
pure Quit, and the prescribed mixture all have value `1`.

For owner 1, write the coordinate in its block as

```text
V_(1,k)(1)=B_1+a_1^(-k)(y_1-B_1).
```

Here `y_1-B_1=-delta/(4d)<0`, while `0<a_1<1`.  Therefore

```text
V_(1,k+1)(1) <= V_(1,k)(1).
```

When owner 1 chooses Continue, all opponents continue surely at that phase,
so its Continue value is exactly `V_(1,k+1)(1)`, which is weakly below the
current value.  Thus for every phase and every player the pure-Continue
branch is at most the current phase value.  This is a favourable inequality,
not an omitted error term.

### 5. Global Snell supersolution and arbitrary deviations

Put

```text
hmax(delta,m)=max(h_m(delta),h_m(1/2)),
e(delta,m)=eta_delta+D*hmax(delta,m).
```

For a fixed deviator define the time-dependent supersolution

```text
S_t=V_t(i)+e(delta,m).
```

The Quit bound in Step 3 puts the immediate-Quit branch below `S_t`.  For a
passive player or owner 0, inserting `S_(t+1)` into the Continue branch adds
the opponents' continuation mass times `e`, which is at most `e`; exact
Continue evaluation therefore puts this branch below `S_t`.  For owner 1 in
its own block the opponents' continuation mass is one, but Step 4 gives

```text
V_(t+1)(1)+e <= V_t(1)+e=S_t.
```

Hence `S` dominates both pure actions at every live history, and therefore
dominates every randomized action.

The opponent-only survival products through a complete cycle are exactly

```text
1/2             for deviator 0,
1-delta         for deviator 1,
(1-delta)/2     for deviators 2 and 3.
```

All are strictly below one.  Iterating the Bellman comparison for a finite
number of cycles leaves a residual bounded by `2M` times the corresponding
opponent-survival probability; this residual tends to zero.  It follows that
for every player `i` and every randomized history-dependent behavioral
replacement `tau_i`, including Never and every arbitrarily late clock,

```text
U_i(profile(delta,m)[i <- tau_i])
 <= U_i(profile(delta,m))+e(delta,m).
```

Thus the mesh cycle is terminal `e(delta,m)`-Nash against the unrestricted
behavioral strategy class, and its exact terminal payoff is `y`.

### 6. Fixed target and uniform-horizon quantifiers

Let `alpha>0`.  First choose `delta` so small that

```text
eta_delta < alpha/2,
3delta/(4(1+delta)) < alpha.
```

For this fixed `delta`, choose `m` so large that

```text
D*hmax(delta,m) < alpha/2.
```

The resulting single periodic behavioral profile is terminal `alpha`-Nash
and its terminal payoff is coordinatewise within `alpha` of the fixed target
`B`.  This proves terminal target acceptance at every positive accuracy.

The finite quitting-game terminal-to-uniform theorem now gives the required
quantifiers: for each requested `epsilon`, it selects one sufficiently
accurate terminal profile and one threshold after which that same profile is
an `epsilon`-Nash equilibrium at every finite average horizon and delivers
`B` within `epsilon`.  The threshold may grow as `delta` shrinks.  No
interchange of `delta`, profile, horizon, or deviation quantifiers is used.

This completes the proof.

## Boundary tests and falsification attempts

1. **Pure boundary screen does not prove a gap.**  For the motivating
   Candidate C table, every Boolean stationary root has positive
   exploitability and the exact pure-toggle floor is `1/4`.  The theorem
   supplies terminal error tending to zero anyway.
2. **Known finite chambers were passed.**  Exact enumeration rejects every
   prescribed two- and three-player persistent-base Nash face and every
   ordered two-date threat chamber recorded in
   `CODEX_RIEMANN__PERSISTENT_PAIR_CHAMBER_NO_GO.md`.
3. **Prior all-behavior upper witness.**  The motivating table already had an
   exact eight-date profile with unrestricted exploitability
   `3069083213250743827/10^20`; the present construction explains and
   strengthens that numerical trend to zero.
4. **Large arbitrary collisions.**  Nonsingleton rewards can be arbitrarily
   large but finite.  They only enlarge `M`; after `delta` is selected, a
   larger `m` makes `2M hmax` as small as required.  No nonsingleton sign is
   hidden in the theorem.
5. **The singular endpoint is not used as a profile.**  Setting `delta=0`
   destroys deleted-opponent contraction for player 1.  The proof always
   uses `delta>0` and only lets its selected payoff approach `B` across the
   outer accuracy choice.
6. **A sure second block is unnecessary.**  Hazard `1` would not admit the
   logarithmic subdivision used here.  The fixed total hazard `1/2` already
   gives contraction and the desired limiting target.
7. **Wrong one-sided sign would break the proof.**  The owner-1 Continue
   argument uses `y_1<B_1` and the resulting decreasing microblock.  The
   theorem makes no claim for a singleton matrix with the opposite sign.

Independent reviewer `CODEX_SPINOZA` recomputed the coarse algebra, endpoint
defects, collision bound, owner-1 Continue orientation, deleted-player
products, and uniform quantifier order, and reported PASS.  A second reviewer
is being asked specifically to falsify the unrestricted Snell comparison and
44-coordinate scope before promotion.

## Adapter and consumer

The actual-data adapter is literal: inspect the four singleton rows of any
Fin4 reward table.  If they equal the four rows in the exact statement,
compute its finite reward bound `M`; for each requested terminal accuracy,
choose `delta,m` as in Step 6 and return the explicit `2m`-phase singleton
cycle of Step 2.  No solver, compactness selection, or nonsingleton condition
is required.

The downstream checked semantic consumer is

```text
quittingGame_isUniformEquilibriumPayoff_of_terminalTargetAcceptance
```

in
`UniformEquilibrium/Quitting/Terminal/TargetTail/TerminalUniformPayoffSelection.lean`.
It accepts terminal approximate Nash profiles approaching one fixed target
and proves precisely the uniform-equilibrium-payoff statement above.  The
equivalent sequence consumer
`quittingGame_isUniformEquilibriumPayoff_of_terminalNash_tendsto` also
applies.

## Source correspondence

The motivating exact table and prior boundary screens are in

* `experiments/codex_riemann_inert_perturbation_search.py`; and
* `notes/CODEX_RIEMANN__PERSISTENT_PAIR_CHAMBER_NO_GO.md`.

Existing checked Lean supplies:

* `quittingSingletonArcCycleRoot`, `quittingSingletonArcCycleValue`, and the
  exact interpolation/closure algebra in
  `UniformEquilibrium/Quitting/Cycles/SingletonArcCycle.lean`;
* `quittingMeshHazard` and the rpow mesh identities in
  `UniformEquilibrium/Quitting/Circulation/SingletonFlowMesh.lean`;
* the local singleton Quit/collision formulas in
  `UniformEquilibrium/Quitting/Stationary/SingletonStationaryRoot.lean`;
* the unrestricted cyclic Snell proof
  `quittingCyclicHazardTerminalValue_le_add_of_quitError_exactContinue` in
  `UniformEquilibrium/Quitting/Cycles/CyclicSupersolution.lean`; and
* the fixed-target consumer named above.

The new mathematical content is the exact Candidate C coarse cycle, the
uniform `eta_delta` endpoint defect, the favourable owner-1 Continue
inequality, and their combination into an approximate-active singleton-mesh
certificate.  No paper theorem is used.

## Lean handoff

The narrow reusable addition is a cyclic Snell lemma whose Continue premise
is an inequality rather than equality:

```text
hcontinue : continueReward phase who
  + continueMass phase who * value(next phase) who
  <= value phase who.
```

The proof of
`quittingCyclicHazardTerminalValue_le_add_of_quitError_exactContinue` already
uses equality only to establish this Bellman branch, so the generalized proof
should be a direct weakening.  A behavioral wrapper should mirror
`isεAsymptoticNash_quittingCyclicBehaviorProfile_of_quitError_exactContinue`.

Then define a specialized Fin4 Candidate C certificate or direct theorem
with:

* owners `[0,1]`, hazards `[delta,1/2]`;
* coarse values `x,y` above;
* `m`-mesh roots and interpolants from `SingletonArcCycle`;
* local error `delta/(2(1+delta))+2M*hmax(delta,m)`;
* exact deleted-player products `1/2`, `1-delta`, and
  `(1-delta)/2`; and
* exact terminal value `y`.

The final theorem should quantify over an arbitrary reward table satisfying
only the four singleton-row equalities and conclude

```text
(quittingGame reward).IsUniformEquilibriumPayoff none B.
```

Finite tests should check the four coarse coordinate identities, monotonicity
of player 1's owner block, the three product values, and independence from a
symbolic nonsingleton reward coordinate.  The conference packet must not be
imported or encoded as an axiom.

## Scope and nonclaims

This theorem does not:

* prove the finite-quitting uniform-equilibrium conjecture;
* classify singleton matrices near Candidate C;
* show completeness of stationary, periodic, or singleton-mesh strategies;
* bound one common mesh size uniformly over the unbounded 44-dimensional
  fibre;
* give a stationary or exact terminal Nash equilibrium for Candidate C; or
* carry a Lean proof before the weakened Continue-interface theorem and the
  specialized adapter are checked.

It is a special-class existence theorem with an unrestricted behavioral
consumer, not a counterexample and not a bounded-search result.
