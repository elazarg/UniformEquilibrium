# Tight-Face Collision and Semantic-Debt Escape for Paid Near-Returns

Authors: `CODEX_NOETHER`, `CODEX_GAUSS`

Independent reviews:

- [`CODEX_NOETHER`, strict-covector source theorem](../feedback/CODEX_GAUSS__CURL_FREE_TOGGLE_POTENTIAL__BY_CODEX_NOETHER__ROUND_15.md);
- [`CODEX_GAUSS`, local escape and collision localization](../feedback/CODEX_NOETHER__QUIT_TIME_COMPACTIFICATION__BY_CODEX_GAUSS__ROUND_47.md);
- [`CODEX_GAUSS`, one-row semantic lift](../feedback/CODEX_NOETHER__QUIT_TIME_COMPACTIFICATION__BY_CODEX_GAUSS__ROUND_48.md);
- [`CODEX_GAUSS`, coherent semantic-path telescope](../feedback/CODEX_NOETHER__QUIT_TIME_COMPACTIFICATION__BY_CODEX_GAUSS__ROUND_49.md).

The first review independently checks the strict separator used as input.
The latter three independently reconstruct the new path estimates and their
composition.  No mathematical objection remains in the stated scope.

## Exact statement

Let `I` be a nonempty finite player set and let

```text
r : {nonempty coalitions S of I} -> (I -> Real)
```

be a finite quitting-game reward table.  At each live date every player
independently chooses Continue or Quit.  If the nonempty set `S` Quits, the
game ends with payoff `r(S)`; if everyone Continues, the unique live state is
repeated.

For a product root `p=(p_i)_(i in I)`, write

```text
Q(p) = 1-product_i(1-p_i),
C(p) = probability that at least two players Quit,
O_i(p) = product_(j != i)(1-p_j).
```

Thus `Q` is one-row absorption, `C` is one-row collision mass, and `1-O_i`
is the probability that at least one opponent of player `i` Quits.  When
`Q>0`, put `zeta(p)=C(p)/Q(p)`; when `Q=0`, put `zeta(p)=0`.

A finite **exact floor-admissible Nash--Bellman path**, in relation
orientation, is

```text
x_0 --p_0--> x_1 --p_1--> ... --p_(m-1)--> x_m.       (1)
```

At edge `t`, `x_t` is the continuation payoff, `p_t` is an independent
product root, and `x_(t+1)` is its exact one-row expected payoff.  Neither
forcing any one player to Quit nor forcing that player to Continue improves
on `x_(t+1)`, and every displayed state satisfies the given playerwise
punishment floors.  This is the orientation of the checked punishment-floor
charged relation: Bellman tail is source and current payoff is target.  Put

```text
charge(path)    = sum_(t<m) Q(p_t),
Collision(path) = sum_(t<m) C(p_t).                  (2)
```

Choose a payoff vector `b`, a nonempty owner set `E subset I`, a nonzero
covector `ell`, and `kappa>0` such that every probability vector `mu`
supported on `E` satisfies the strict singleton-row separation

```text
ell dot (b-sum_(j in E) mu_j r({j})) >= kappa.       (3)
```

Let

```text
L = sum_i |ell_i|,
R = max_(nonempty S,i) |r(S)_i|,
B = max(1,R),
epsilon_0 = kappa/(4L),
zeta_0 = min(1/2,kappa/(8BL)).                        (4)
```

The nonzero separator makes `L>0`; all displayed constants are therefore
well-defined and positive except that `R` may be zero.

### Theorem A: local tight-face paths must escape or collide

Assume every vertex `x_t` of `(1)` is within `epsilon_0` of `b` in sup norm,
and every positive Quit coordinate of every root belongs to `E`.  Then

```text
ell dot (x_0-x_m)
  >= (3*kappa/4)*charge(path)-2*B*L*Collision(path).  (5)
```

If every edge also has `zeta(p_t)<=zeta_0`, then

```text
ell dot (x_0-x_m) >= (kappa/2)*charge(path).          (6)
```

In particular, if some edge has `Q(p_t)>=a>0`, then

```text
||x_0-x_m||_infinity >= kappa*a/(2L).                (7)
```

Equivalently, any exact path having a fixed high edge and endpoints closer
than the right side of `(7)` must do at least one of the following:

1. leave the `epsilon_0` payoff neighborhood of `b`;
2. activate a Quit owner outside `E`; or
3. contain an edge with conditional collision fraction greater than
   `zeta_0`.

Even without a rowwise collision bound, if the first two alternatives are
absent, some edge has `Q>=a`, and

```text
||x_0-x_m||_infinity <= kappa*a/(4L),                (8)
```

then the whole path has the fixed absolute collision budget

```text
Collision(path) >= kappa*a/(4BL).                    (9)
```

Suppose additionally that one constant `P_0` bounds the charge of every
floor-admissible path under consideration.  Put

```text
gamma = kappa*a/(4BLP_0),
N_pair = choose(|I|,2).
```

Then `(9)` localizes to one literal edge `p` with

```text
zeta(p) >= gamma,
Q(p) >= gamma/N_pair,
C(p) >= gamma^2/N_pair.                              (10)
```

The positive left side of `(9)` forces `N_pair>0`, so no division-by-zero
case is hidden in `(10)`.

### Theorem B: one semantic source lift pays every collision on the path

For a behavioral profile `sigma`, let

```text
v_i(sigma) = prescribed terminal payoff of player i,
h_i(sigma) = supremum terminal payoff attainable by replacing
             player i's entire behavioral stopping strategy,
d_i(sigma) = h_i(sigma)-v_i(sigma).
```

The **terminal-semantic carrier** `K(r)` is the closure of the set of pairs
`(v(sigma),h(sigma))` over all behavioral profiles.  Its debt coordinates
`d_i=h_i-v_i` are nonnegative.  Let `(v_*,h_*)` minimize total debt on this
compact carrier and put

```text
D_* = sum_i (h_*,i-v_*,i).
```

Assume `D_*>0`.  Suppose the path source has one carrier lift: there is
`pair_0=(x_0,h_0)` in `K(r)`.  Prefix it recursively by the displayed roots.
For a pair `(v,h)` and a root `p`, the prefixed prescribed coordinate is the
one-row successor payoff against continuation `v`; player `i`'s prefixed
envelope is the maximum of

- forced Quit against the opponents' root, with continuation `v`; and
- forced Continue, using `h_i` rather than `v_i` on the event that every
  opponent Continues.

Call the resulting pair `pair_(t+1)` and write `D_t` for its total debt.
Then every `pair_t` remains in `K(r)`, its prescribed payoff is exactly
`x_t`, and

```text
C(p_t)*D_t <= D_t-D_(t+1),                           (11)
D_* * Collision(path) <= D_0-D_m <= D_0-D_*.        (12)
```

Consequently a positive-collision exact path starting on the minimum fiber
is impossible.  Combining `(9)` and `(12)`, under the local tight-face and
near-return hypotheses of Theorem A,

```text
D_0-D_* >= D_* * kappa*a/(4BL).                      (13)
```

Thus a fixed-charge local payoff near-return with terminal-semantic source
provenance cannot start arbitrarily close to the positive minimum-debt fiber.

## Conjecture-facing change

The named live obligation is `PAID_ADMISSIBLE_PAYOFF_NEAR_RETURN`: from the
paid first-disagreement branch, construct one fixed `a>0` and, for every
endpoint tolerance, an exact punishment-floor path with an edge of absorption
at least `a` and arbitrarily close endpoint payoffs.  The checked consumer
allows the source, target, path, length, roots, supports, and high edge all to
vary with the tolerance.

Before this result, that family could conceivably have been obtained by a
diffuse recurrence remaining near the residual-hard boundary payoff, using
only boundary-tight owners and resetting through the positive minimum
terminal-semantic fiber.  Theorems A--B rule out exactly that local mechanism:

- collision-light motion in the tight face is strictly monotone in one fixed
  covector and cannot return;
- an endpoint-close path that stays there must carry a fixed absolute
  simultaneous-quitter budget, and under the canonical prefix-capacity bound
  contains one macroscopic collision row; and
- if one terminal-semantic source lift is retained, that collision budget
  forces one fixed positive excursion above minimum total debt already at the
  path source.

The remaining producer must therefore make a nonlocal payoff excursion,
activate an owner outside the tight face, or construct a source-matched
high-debt collision excursion and return.  This is a strict reduction of the
named paid-row obligation, not a construction of its requested family.

## Definitions, probability mode, and unilateral agency

All root probabilities in this packet are finite independent product laws.
Coalition delivery is literal: the probability of `S` is

```text
product_(i in S) p_i * product_(i notin S)(1-p_i).
```

No conditional law is used when `Q=0`.  When `Q>0`, conditioning is only on
the event that at least one player Quits.  Ties are simultaneous coalitions,
not an ordering convention.  The path itself is finite and introduces no
Never event.

The endpoint-Nash field is exact at every row and compares both pure actions
of each current player.  Theorem B's envelope is stronger: one player may
replace their entire behavioral strategy along the infinite live history.
The other players' strategies and all terminal rewards remain fixed.  Thus
semantic debt is unrestricted unilateral exploitability, not stationary or
one-shot regret.  Prefixing is valid because a quitting game has one public
live history and the deviator observes whether play has survived to it.

The packet itself proves a geometric and semantic obstruction.  Its
downstream uniform-payoff conclusion comes only through the already checked
near-return consumer described below, which covers unrestricted behavioral
deviations.

## Source correspondence and novelty audit

The narrow source search used `strict covector`, `payoff near return`,
`collision mass`, `terminal semantic prefix`, and `debt drift`.  The relevant
existing declarations are:

- `exists_strictCovector_on_tightOwners_of_no_uniformPayoff` and
  `exists_eventual_strictCovectorCharge_of_no_uniformPayoff`
  (`UniformEquilibrium/Diagnostics/Quitting/Chronology/StrictCovectorDynamicTail.lean`).
  These are the checked actual-data adapter for `(3)` on the nonplateau
  residual-hard tail.  The packet does not re-prove that source theorem.
- `IsQuittingNashBellmanEdge.eq_collisionAwareSegment`
  (`UniformEquilibrium/Quitting/Cycles/CollisionAwareFiniteReturn.lean`) gives
  the exact affine Bellman identity used in Theorem A.
- `quittingRootCollisionMass_le_opponentAbsorptionMass` and
  `quittingRootCollisionMass_mul_sum_le_sum_opponentAbsorptionMass_mul`
  (`UniformEquilibrium/Quitting/AbsorptionPath/CollisionConcentration.lean`)
  package the elementary event inclusions used in Theorem B.
- `quittingTerminalSemanticPair_mem_carrier` and
  `quittingTerminalSemanticPrefix_mem_carrier`
  (`UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticPlateauIncidence.lean`
  and `UniformEquilibrium/Quitting/Root/TerminalSemanticPair.lean`) are the
  actual-profile lift and coherent-prefix adapter.
- `sum_opponentAbsorptionMass_mul_debt_le_sumDebt_drift_add_totalNashDefect`
  (`UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticPlateauDefectCharge.lean`)
  is a checked one-row version of the debt estimate; exact Nash sets its
  defect term to zero.
- `QuittingPunishmentFloorAdmissibleChargedRelation.pathToFinitePrefix_charge`
  and `QuittingTerminalExploitabilityWitness.prefixCharge_le`
  (`UniformEquilibrium/Quitting/Bellman/Finite/PunishmentFloorAdmissibleChargedRelation.lean`
  and `UniformEquilibrium/Quitting/Terminal/TerminalExploitabilityWitness.lean`)
  supply the canonical `P_0` adapter used only for `(10)`.
- `quittingRootCollisionMass_le_choose_card_mul_absorption_sq`
  (`UniformEquilibrium/Quitting/AbsorptionPath/CollisionConcentration.lean`)
  localizes the aggregate collision budget to `(10)`.

There are two nearby results which this packet does not duplicate.
`causalCollision_tailEscape_or_quantitativeBestEndpoint`
(`UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticLawCarrierCausalNashDispatch.lean`)
is a stronger actual-profile one-row dichotomy.  It does not give the common
strict-covector telescope for arbitrary exact relation paths or show that one
source carrier lift propagates coherently through a whole selected path.
`sum_stageCollisionMass_mul_tailDebtSum_le_stoppedDefectExcess`
(`UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticPlateauDefectTelescope.lean`)
is an actual-profile stopped telescope with live-mass weights and Nash-defect
terms.  Theorem B instead applies to an arbitrary finite exact relation path;
exact selected roots remove the defect term, and one supplied source lift
provides the complete semantic chronology.

No paper theorem is used.  In particular, this is not presented as a new
translation of a Solan--Vieille or Simon result.  The new ordinary-mathematics
content is the quantitative composition `(5)--(13)` and its strict
restriction of the paid near-return interface.

## Proof

### 1. One-edge singleton/collision decomposition

Fix an edge and abbreviate its tail by `y`, its current payoff by `x`, its
root absorption by `Q`, and its conditional absorbing delivery by `D` when
`Q>0`.  Exact Bellman evaluation gives

```text
x=(1-Q)y+QD,
y-x=Q(y-D).                                           (14)
```

If `Q=0`, then `x=y` and `C=0`, so the desired one-edge contribution is zero.
Suppose `Q>0` and put `zeta=C/Q`.

If `zeta<1`, normalize the exact singleton atoms to a probability vector
`mu`.  A positive singleton atom for owner `j` implies `p_j>0`, so the support
hypothesis places `mu` on `E`.  Let `R_single` be its singleton reward
mixture and let `R_collision` be the conditional mixture of all coalitions
of size at least two.  Then

```text
D=(1-zeta)R_single+zeta R_collision.                 (15)
```

If `zeta=1`, the singleton coefficient is zero; choose any `mu` on the
nonempty set `E`, and `(15)` remains exact.  Both reward mixtures lie in the
coordinate box `[-R,R]`, hence

```text
||D-R_single||_infinity <= 2R*zeta.                  (16)
```

The separator, the local payoff bound, and
`|ell dot u|<=L||u||_infinity` give

```text
ell dot (y-D)
 >= kappa-L||y-b||_infinity-2RL*zeta
 >= 3*kappa/4-2BL*zeta.                              (17)
```

Multiplying by `Q` in `(14)` gives the one-edge version of `(5)` because
`Q*zeta=C`.

### 2. Path telescope and collision localization

Sum `(17)` along `(1)`.  Every intermediate payoff cancels with the relation
orientation shown in `(1)`, proving `(5)`.  If every `zeta<=zeta_0`, then

```text
Collision(path) <= zeta_0*charge(path),
```

and `(4)--(5)` leave coefficient at least
`3*kappa/4-kappa/4=kappa/2`; this proves `(6)`.  A high edge gives
`charge(path)>=a`, and the finite-dimensional dual norm bound gives `(7)`.

Under `(8)`, the absolute value of the left side of `(5)` is at most
`kappa*a/4`, while its positive charge term is at least `3*kappa*a/4`.
Rearrangement proves `(9)`.

Now assume `charge(path)<=P_0`.  Since

```text
Collision(path)=sum_t Q(p_t)*zeta(p_t),
```

some edge has

```text
zeta(p_t) >= Collision(path)/charge(path) >= gamma.
```

For an independent product law, every collision contains a pair of Quitters;
a union bound over pairs gives

```text
C(p) <= choose(|I|,2)*Q(p)^2,
zeta(p) <= N_pair*Q(p).
```

Therefore `Q(p)>=gamma/N_pair` and
`C(p)=Q(p)zeta(p)>=gamma^2/N_pair`, proving `(10)`.

### 3. Prefixing one terminal-semantic source

For a literal profile, prefixing a fixed product root produces another
literal profile, and its prescribed payoff/envelope pair is exactly the
prefix operation stated in Theorem B.  That operation is continuous in the
finite-dimensional pair.  It therefore preserves the closure `K(r)`.  By
induction, every `pair_t` lies in `K(r)` and has prescribed coordinate `x_t`.

Fix player `i`.  Let `d_(t,i)>=0` be their debt in `pair_t`.  Exact root Nash
against `x_t` says that forced Quit and forced Continue, evaluated with
continuation `x_t`, are both at most the prescribed successor
`x_(t+1,i)`.  Replacing only the all-opponents-Continue continuation
coordinate by the envelope adds exactly `O_i(p_t)*d_(t,i)` to forced
Continue and changes forced Quit by zero.  Hence the prefixed envelope obeys

```text
d_(t+1,i) <= O_i(p_t)*d_(t,i),
(1-O_i(p_t))*d_(t,i) <= d_(t,i)-d_(t+1,i).           (18)
```

Every collision includes an opponent of each fixed player, so

```text
0 <= C(p_t) <= 1-O_i(p_t).                           (19)
```

Multiply `(19)` by the nonnegative debt, apply `(18)`, and sum over players:

```text
C(p_t)*D_t <= D_t-D_(t+1).
```

This is `(11)`.  In particular total debt is nonincreasing.  Every prefixed
pair remains in `K(r)`, so `D_t>=D_*`.  Multiply each collision by that lower
bound, sum `(11)`, and telescope:

```text
D_* sum_t C(p_t)
 <= sum_t C(p_t)D_t
 <= D_0-D_m
 <= D_0-D_*.
```

This proves `(12)`.  Combining it with `(9)` proves `(13)`.

## Boundary tests

1. **Singleton-only paths.**  If every edge has at most one positive Quit
   owner, every collision mass is zero.  Equation `(5)` becomes a strict
   monotonicity law, so a fixed-charge local tight-face return is impossible.
2. **Pure-collision boundary.**  If `zeta=1`, the singleton mixture is
   irrelevant and the full `2BL*C` error in `(5)` remains.  This verifies why
   the collision arm cannot be deleted from the trichotomy.
3. **Minimum semantic fiber.**  If `D_0=D_*>0`, `(12)` forces every
   nonnegative collision mass on the path to vanish.  This is the exact
   positive-minimum boundary used by the reduction.
4. **Zero minimum debt.**  If `D_*=0`, `(12)` has no coercive content.  The
   theorem deliberately makes no claim on the zero-debt branch.
5. **One player.**  Then collision mass and opponent absorption are both
   zero.  The debt telescope is exact but vacuous, and `(10)` is never
   invoked because `(9)` cannot be positive.
6. **Outside-face activation is essential.**  Take two players,
   `b=(0,0)`, `E={0}`, `r({0})=(0,-1)`,
   `r({1})=(20,-1)`, `r({0,1})=(0,0)`, and `ell=(1/10,1)`.  The tight singleton row has
   `ell dot(b-r({0}))=1`, while the outside row has
   `ell dot(b-r({1}))=-1`.  Notice that player `1` still has own solo reward
   `-1<=b_1`; the reversal comes from its off-diagonal reward.  Thus support
   in `E` cannot be omitted.
7. **Locality is essential.**  In the same table, the tight singleton
   delivery is `(0,-1)`.  At the tail `y=(0,-2)`,
   `ell dot(y-r({0}))=-1`, whereas at `b` it is `1`.  The radius
   `epsilon_0` records the exact local perturbation absorbed in `(17)`.
8. **Semantic provenance is essential.**  A counterfactual exact Bellman tail
   need not be the payoff coordinate of any point of `K(r)`.  Theorem A still
   applies to such a path, but `(11)--(13)` do not: no artificial debt vector
   may be attached in place of the source lift.

## Adapter and consumer

The actual-data adapter has two checked parts.  On the residual-hard
nonplateau branch,
`exists_strictCovector_on_tightOwners_of_no_uniformPayoff` supplies the
literal boundary payoff, tight owner set, covector, and positive separation
constant in `(3)`.  A literal behavioral source profile supplies its exact
terminal-semantic pair through `quittingTerminalSemanticPair_mem_carrier`;
one such source lift then propagates through the whole exact path by the
prefix operation.  No independently selected semantic lift at later states
is required.

For the macroscopic-row refinement, the exact path-to-prefix decoder and the
canonical terminal-exploitability charge bound supply `P_0`.  All roots,
coalition probabilities, rewards, and payoff coordinates remain those of the
original reward table; no completion table or stationary-only verifier is
used.

The downstream all-behavior consumer is
`quittingGame_exists_uniformEquilibriumPayoff_of_admissiblePath_payoffNearReturns`
and its packaged input `QuittingPositiveAdmissiblePayoffNearReturnFamily`
(`UniformEquilibrium/Quitting/Projective/PunishmentFloorNearReturn.lean`).
The paid-row interface is
`PaidFirstDisagreementAdmissiblePayoffNearReturnConsumer`, and the generic
capstone is
`exists_uniformEquilibriumPayoff_of_finiteSupportRankExitPayoffNearReturnConsumers`
(`UniformEquilibrium/Diagnostics/Quitting/PaidFirstDisagreementPayoffNearReturn.lean`).

The packet supplies a necessary reduction for that producer interface, not
the family consumed by it.  A future positive construction must cross one of
the three explicit escape arms and, if it preserves a semantic source lift
through the collision arm, must pay the debt height `(13)`.

## Lean handoff

1. Introduce a small `TightFaceSeparatorData` structure containing `b`, `E`,
   `ell`, `kappa`, `E.Nonempty`, and `(3)`.  Do not store any path conclusion
   as a field.  Add an adapter from
   `exists_strictCovector_on_tightOwners_of_no_uniformPayoff`.
2. Define path collision mass as the finite sum of
   `quittingRootCollisionMass` over the existing charged-relation path.
   Prove the one-edge inequality first from
   `IsQuittingNashBellmanEdge.eq_collisionAwareSegment`, with separate
   `Q=0` and `zeta=1` branches.
3. Sum the one-edge inequality to obtain `(5)`, then prove `(6)--(10)` as
   separate corollaries.  Reuse the existing path charge decoder and product
   collision bound.
4. For Theorem B, use the existing `quittingTerminalSemanticPrefix` rather
   than defining a new semantic state.  Prove `(18)` directly from exact root
   Nash, or specialize
   `sum_opponentAbsorptionMass_mul_debt_le_sumDebt_drift_add_totalNashDefect`
   and eliminate its Nash-defect term with exact Nash.
5. State the final composition as a theorem about a supplied exact
   punishment-floor path, one source carrier lift, a high edge, and endpoint
   closeness.  It should output the explicit debt lower bound `(13)`; it
   should not assume that bound in an input structure.
6. Finite regression tests should cover `Q=0`, one active owner, pure
   collision, one player, `D_*=0`, and `D_0=D_*>0`.

Likely narrow imports are the files named in the source audit plus
`UniformEquilibrium/Quitting/Bellman/Finite/PunishmentFloorAdmissibleChargedRelation.lean`.
The theorem should remain game-semantic: the finite-dimensional separator
lemma alone may be isolated in `MathUE` only if it has no quitting imports.

## Scope and nonclaims

- This packet does not construct a paid admissible payoff near-return, a
  high-debt source, a collision gadget, or a return from a debt excursion.
- It does not prove the finite-quitting uniform-equilibrium conjecture and is
  not a game counterexample.
- It does not say that every admissible path has a terminal-semantic source
  lift.  Literal actual-profile sources do; counterfactual Nashified tails may
  not.
- It does not exclude paths that leave the local payoff ball, activate an
  owner outside `E`, or carry nonperturbative collision.  Those are the exact
  surviving mechanisms.
- The prefix-capacity constant `P_0` is used only for the one-row localization
  `(10)`, not for the aggregate inequalities `(5)--(9)` or debt telescope.
- The strategy-class statement is unrestricted only in the definition of
  terminal-semantic debt and in the checked downstream consumer.  The path
  roots themselves are finite independent product laws.
- No claim is made for general finite stochastic games; the proof uses the
  single live history and coalition terminal rewards of finite quitting
  games.
