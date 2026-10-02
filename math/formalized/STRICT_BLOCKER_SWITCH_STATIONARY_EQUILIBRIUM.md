# Strict Blocker-Switch Stationary Equilibrium

Authors: `CODEX_GAUSS`
Independent reviews:
[`CODEX_NOETHER`](../feedback/CODEX_GAUSS__CURL_FREE_TOGGLE_POTENTIAL__BY_CODEX_NOETHER.md),
[`CODEX_CEDAR`](../feedback/CODEX_GAUSS__CURL_FREE_TOGGLE_POTENTIAL__BY_CODEX_CEDAR__ROUND_2.md)

## Exact statement

Let `I` be a nonempty finite player set.  Let

`r : {S subset I | S nonempty} -> (I -> R)`

be a finite quitting-game reward table, with terminal payoff zero when nobody
ever Quits.  Let `pi : I -> I` be a permutation with `pi(i) != i` for every
player.

Assume:

1. **Passive continuers.**  For every nonempty quitting coalition `S` and
   every `i notin S`,

   `r(S)_i=0`.

2. **Strict blocker switch.**  For every player `i` and every coalition
   `T subset I-{i,pi(i)}`,

   `r(T union {i})_i>0`,

   `r(T union {i,pi(i)})_i<0`.

Then there is a vector `p in (0,1)^I` such that the stationary behavioral
profile in which player `i` Quits independently with probability `p_i` at
every live history is an exact terminal Nash profile against every unilateral
behavioral deviation.  Its terminal payoff is the zero vector, and zero is a
uniform-equilibrium payoff of the quitting game.

This theorem and its actual reward-table adapter are proved in Lean by the
declarations cited below.

## Conjecture-facing change

The result gives a new positive special-case producer for arbitrary finite
player count, including the open range of the finite-quitting conjecture.  Its
input is a finite family of equalities and strict inequalities on the actual
reward table, together with a fixed-point-free blocker permutation.  Its
output is an explicit kind of semantic object: a fully mixed stationary exact
terminal Nash profile with fixed target zero.

The result is not a universal producer.  It does not close either open
producer arrow in `docs/FRONTIER.md`, and it does not assert the blocker
hypotheses for an arbitrary reward table.

## Definitions and assumptions

For `p in [0,1]^I` and player `i`, let `Q_i(p)` be the expected payoff from
choosing pure Quit at the current live stage while every opponent `j` Quits
independently with probability `p_j`.  Explicitly,

`Q_i(p) = sum_(T subset I-{i}) mu_(p,-i)(T) r(T union {i})_i`,

where

`mu_(p,-i)(T) = product_(j in T) p_j *
                 product_(j notin T, j != i) (1-p_j)`.

This is a finite multiaffine polynomial and is independent of `p_i`.

The constructed strategy uses only the private independent randomization
already allowed in a behavioral profile.  At every public live history each
player uses the same Bernoulli law.  No public signal, correlating device,
additional state, or observation within a stage is assumed.

The equilibrium comparison is terminal and covers replacement of one
player's entire behavioral strategy.  The uniform-payoff target is the one
fixed vector zero; it does not depend on the requested accuracy.

## Source correspondence

The open target is `quittingUniformEquilibriumPayoffConjecture`
(`UniformEquilibrium/Quitting/Conjecture/Basic.lean`).

The checked downstream declarations are:

- `isZeroAsymptoticNash_stationary_of_fixedPoint_endpointNash_contracts`; and
- `isUniformEquilibriumPayoff_of_stationaryEndpointCertificate_contracts`

(`UniformEquilibrium/Quitting/Stationary/EndpointCompiler.lean`).  They consume
a jointly absorbing stationary fixed point, exact endpoint Nash, and
playerwise opponent contraction.  Their deviation class is all behavioral
strategies.  The new ordinary mathematics below produces those inputs from
the raw blocker-switch table.

Nearby existing positive classes do not subsume the full statement as a named
actual-data adapter:

- `quittingGame_exists_uniformEquilibriumPayoff_of_card_eq_three`
  (`UniformEquilibrium/Quitting/Classification/PlayerReindex.lean`) already
  covers every three-player example at the existence level.
- The uniform five-cycle center with blocker rewards `+1/-1` is covered by
  `exists_uniformEquilibriumPayoff_colliderReward`
  (`UniformEquilibrium/Quitting/Classification/Circulant/TerminalExploitabilityColliderClosure.lean`).
- `quittingGame_exists_uniformEquilibriumPayoff_of_cardinalSymmetric`
  (`UniformEquilibrium/Quitting/Classification/SymmetricQuittingGame.lean`)
  covers fully symmetric tables, whereas blocker permutations and the reward
  magnitudes here may be asymmetric.
- `exists_stationaryUniformEquilibriumPayoff_or_standardQMatrixSide`
  (`UniformEquilibrium/Quitting/Classification/LCP/StationaryExistence.lean`)
  is a broad conditional LCP classification.  It does not state the raw
  blocker-sign adapter or construct the root below.

The narrow Literature audit found no duplicate paper statement.  In
particular, the Solan--Solan (2020) transcription uses a standing zero-solo
normalization, while strict blocker switch makes every singleton self-reward
positive.  The Flesch--Thuijsman--Vrieze (1997) example allows nonzero rewards
to continuing players and is explicitly a no-exact-stationary-equilibrium
example, so it is not this family.

The novelty claimed here is narrow: the raw strict blocker-switch producer and
its fully mixed stationary zero certificate for arbitrary finite
fixed-point-free permutations and arbitrary background-dependent quitter
rewards.  No claim is made that the underlying Poincare--Miranda argument is a
new topological theorem.

## Proof

### 1. Opposite signs on paired cube faces

Fix player `i`.  On the face `p_(pi(i))=0`, its blocker surely Continues.
Expanding `Q_i(p)` over the remaining opponents expresses it as a convex
combination of the finitely many numbers

`r(T union {i})_i`, for `T subset I-{i,pi(i)}`.

Every one is strictly positive, so `Q_i(p)>0` everywhere on that face.

On the opposite face `p_(pi(i))=1`, the blocker surely Quits.  The same
expansion is a convex combination of

`r(T union {i,pi(i)})_i`, for `T subset I-{i,pi(i)}`.

Every one is strictly negative, so `Q_i(p)<0` everywhere on that face.

### 2. Poincare--Miranda zero

Reindex the equations by cube coordinates.  For `j in I`, define

`F_j(p)=Q_(pi^{-1}(j))(p)`.

Because `pi` is a permutation, `F_j` is strictly positive on the face
`p_j=0` and strictly negative on the face `p_j=1`.

The Poincare--Miranda theorem gives a zero of `F` in the cube.  Here is the
standard Brouwer reduction, included to fix the signs and boundary behavior.
Define a continuous cube self-map by

`H_j(p)=clamp_[0,1](p_j+F_j(p))`.

Brouwer's fixed-point theorem gives `p` with `H(p)=p`.  This fixed point cannot
have `p_j=0`, because then `F_j(p)>0` and `H_j(p)>0`.  It cannot have `p_j=1`,
because then `F_j(p)<0` and `H_j(p)<1`.  Thus every coordinate lies strictly
between zero and one.  At an interior fixed coordinate the clamp cannot return
the interior value `p_j` from an input outside `[0,1]`; it is inactive, and

`p_j+F_j(p)=p_j`.

Therefore `F_j(p)=0` for every `j`, equivalently `Q_i(p)=0` for every player.

### 3. Exact stationary endpoint certificate

Use the zero vector as continuation target.  At the product root determined
by `p`, player `i`'s pure Quit endpoint is `Q_i(p)=0`.

Its pure Continue endpoint is also zero.  If at least one opponent Quits, the
absorbing coalition omits `i`, so passive continuers gives reward zero.  If
all opponents Continue, the continuation target is zero.  Hence both pure
endpoints are zero.  Every mixed endpoint is their convex combination, so the
prescribed root successor payoff is zero and the root is exact endpoint Nash
at the fixed point zero.

Every `p_i` is positive, so the probability that all players Continue is
strictly below one: the root is jointly absorbing.  For each player `i`, the
distinct opponent `pi(i)` Quits with positive probability.  Consequently the
probability that every opponent of `i` Continues is at most
`1-p_(pi(i))<1`, giving playerwise opponent contraction.

The two checked stationary endpoint corollaries named above now apply.  The
stationary profile is exact terminal Nash against arbitrary behavioral
deviations, and zero is a uniform-equilibrium payoff.  This completes the
proof.

## Boundary tests

### Background dependence is genuinely allowed

Take three cyclic players with `pi(i)=i+1`, and let `k=i+2`.  A continuer gets
zero.  A quitter `i` gets

- `1` if both `pi(i)` and `k` Continue;
- `2` if `pi(i)` Continues and `k` Quits;
- `-1` if `pi(i)` Quits and `k` Continues; and
- `-2` if both opponents Quit.

The strict face signs hold, but the quitter reward is not the two-constant
one-blocker formula.  Here

`Q_i(p)=(1+p_k)(1-2p_(pi(i)))`,

so `p_i=1/2` for all players is the predicted interior zero.  This is a finite
exact test of the background-dependent theorem.  Its existence conclusion is
not novel at three players; the purpose is to test the adapter.

### The mixed construction can be essential for this route

For the same cyclic table, no pure quitting coalition is a sure exit set.  If
both `i` and `pi(i)` Quit, player `i` gets a negative payoff and prefers to
leave, receiving zero as a continuer.  If neither Quits, player `i` prefers to
join and receive a positive payoff.  A sure exit set would therefore require
membership to alternate around a three-cycle, which is impossible.

This does not imply nonexistence: the stationary half-Quit profile above is
the exact equilibrium.

### Strictness is used for interiority

With two players blocking each other, passive continuers, singleton quitter
payoff `1`, and joint quitter payoff `0`, the weak signs hold but

`Q_1(p)=1-p_2`, `Q_2(p)=1-p_1`.

The unique common zero is the boundary root `(1,1)`, not an interior root.
The strict theorem deliberately excludes this boundary.  The game still has
an exact zero equilibrium; this test concerns the adapter's fully mixed
conclusion, not uniform-payoff nonexistence.

### Passive continuers is load-bearing

Start from the symmetric two-player strict table with singleton self-reward
`1`, joint self-reward `-1`, and all continuer rewards zero.  The constructed
root is `(1/2,1/2)`.  If player 1's reward at coalition `{2}` is changed from
zero to a positive number `eta`, while all quitter entries are unchanged,
player 1's Continue endpoint at target zero becomes `eta/2`, whereas its Quit
endpoint remains zero.  The zero endpoint certificate fails.

Thus strict blocker switch is robust only under small perturbations of quitter
entries which preserve the signs while the passive-continuer equalities remain
exact.  The class is relatively open in the passive-continuers affine
subspace, not open in the full reward-table space.

## Adapter and consumer

The adapter starts from actual source data `(r,pi)` satisfying finite raw-table
conditions.  It forms the polynomial Quit-value map `Q`, reindexes it by
`pi`, and uses the paired face signs to produce an interior probability vector
`p`.  No profile, certificate, Nash root, or target selector is assumed as
input.

The produced `(p,0)` packet supplies exactly:

- joint absorption;
- the stationary fixed-point identity at zero;
- exact endpoint Nash; and
- playerwise opponent contraction.

The checked consumer
`isUniformEquilibriumPayoff_of_stationaryEndpointCertificate_contracts`
then reaches the uniform-payoff semantics.  The companion checked theorem
`isZeroAsymptoticNash_stationary_of_fixedPoint_endpointNash_contracts`
records exact terminal Nash for the same stationary profile.

## Checked Lean realization

`exists_positive_hazard_sigmaValue_eq_baseline_of_blockerSwitch` and
`exists_interior_hazard_sigmaValue_eq_baseline_of_strictBlockerSwitch` construct
the root from the raw switch predicate.  The actual-data stationary adapter and
semantic capstone are `exists_stationaryCertificate_of_blockerSwitch` and
`isUniformEquilibriumPayoff_of_blockerSwitch`; strictness additionally yields
`exists_stationaryCertificate_interior_of_strictBlockerSwitch`
(`UniformEquilibrium/Quitting/Classification/Existence/BlockerSwitch.lean`).

## Scope and nonclaims

- The theorem covers a special raw-table class, not every finite quitting game.
- It does not prove the finite-quitting conjecture or the general stochastic-
  game conjecture.
- It does not close the chronological-atom or paid-row universal producer gap.
- It does not cover nonzero continuer rewards.
- Strict signs are used for a fully interior root; weak signs require a
  separate boundary analysis and are not part of this packet.
- The theorem uses a fixed-point-free blocker permutation.  Nonbijective
  blocker maps and multi-equation compatibility are outside this packet.
- The relative openness claim is only inside the exact passive-continuers
  affine subspace.
- The blocker-switch actual-data adapter and unrestricted-behavior semantic
  capstone are proved in Lean; strictness is used only for full interiority.
