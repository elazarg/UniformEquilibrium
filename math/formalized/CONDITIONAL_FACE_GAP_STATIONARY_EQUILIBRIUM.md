# Conditional Face Gaps Produce an Exact Stationary Uniform Payoff

Authors: `CODEX_GAUSS`; five-player adapter proposed by `CODEX_NOETHER`

Independent reviews:

- [general theorem and finite adapter, by CODEX_CEDAR](../feedback/CODEX_GAUSS__CURL_FREE_TOGGLE_POTENTIAL__BY_CODEX_CEDAR__ROUND_3.md)
- [general theorem, falsification of the first witness, and repaired adapter, by CODEX_NOETHER](../feedback/CODEX_GAUSS__CURL_FREE_TOGGLE_POTENTIAL__BY_CODEX_NOETHER__ROUND_2.md)
- [independent audit of the repaired five-player adapter, by CODEX_CEDAR](../feedback/CODEX_GAUSS__CURL_FREE_TOGGLE_POTENTIAL__BY_CODEX_CEDAR__ROUND_4.md)

Source notebook:
[CODEX_GAUSS__CURL_FREE_TOGGLE_POTENTIAL.md](../notes/CODEX_GAUSS__CURL_FREE_TOGGLE_POTENTIAL.md)

## Exact statement

Let `I` be a finite nonempty player set and let

`r : {S subset I | S nonempty} -> R^I`

be the terminal reward table of a quitting game.  At every live date, every
player independently chooses Continue or Quit.  The game absorbs at the first
date whose quitting set is nonempty and pays `r(S)`.

For a product vector `p in [0,1]^I`, interpret `p_i` as player `i`'s Quit
probability.  For `T subset I-{i}`, write

`mu_i(p,T)=product_(j in T) p_j product_(j in I-{i}-T)(1-p_j)`.

Define player `i`'s pure-Quit endpoint, unconditional absorbing Continue
contribution, and all-opponents-Continue mass by

`R_i(p)=sum_(T subset I-{i}) mu_i(p,T) r(T union {i})_i`,

`W_i(p)=sum_(nonempty T subset I-{i}) mu_i(p,T) r(T)_i`,

`c_i(p)=product_(j!=i)(1-p_j)`.

Whenever `c_i(p)<1`, define the conditional continuer value and stationary
gap

`V_i(p)=W_i(p)/(1-c_i(p))`,

`G_i(p)=R_i(p)-V_i(p)`.

Fix a fixed-point-free permutation `pi : I -> I` and reals

`0 < alpha < beta <= 1`.

### Conditional face-gap theorem

Assume that for every player `i` and every `p in [alpha,beta]^I`,

`p_(pi(i))=alpha  ->  G_i(p)>0`,

`p_(pi(i))=beta   ->  G_i(p)<0`.

Then there is a product vector `p* in (alpha,beta)^I` satisfying

`G_i(p*)=0`

for every player.  Put `v=V(p*)`.  Repeating the independent product row
`p*` at every live date gives all of the following:

1. both pure stationary endpoints of every player equal `v_i`;
2. `v` is the one-stage successor payoff of the row;
3. the repeated row is an exact Nash equilibrium for the expected terminal
   payoff functional against replacement of any one player's entire
   behavioral strategy; and
4. `v` is a uniform-equilibrium payoff against unrestricted unilateral
   behavioral deviations.

No public correlating device and no restriction of a deviator to stationary
or bounded-controller strategies is used.

### Finite reward-range corollary

For each player put `K_i=I-{i,pi(i)}` and define the literal reward extrema

`H_i^- = min_(T subset K_i) r(T union {i})_i`,

`H_i^+ = max_(T subset K_i) r(T union {i})_i`,

`L_i^- = min_(T subset K_i) r(T union {i,pi(i)})_i`,

`L_i^+ = max_(T subset K_i) r(T union {i,pi(i)})_i`,

`C_i^- = min_(nonempty S subset I-{i}) r(S)_i`,

`C_i^+ = max_(nonempty S subset I-{i}) r(S)_i`.

If, for every `i`,

`(1-alpha)H_i^- + alpha L_i^- > C_i^+`,

`(1-beta)H_i^+ + beta L_i^+ < C_i^-`,

then the conditional face hypotheses hold and the same conclusion follows.

## Conjecture-facing change

The existing LCP split
`exists_stationaryUniformEquilibriumPayoff_or_standardQMatrixSide` stops
without producing a strategy on `StandardQMatrixSide`.  This packet supplies
a direct exact stationary producer for a concrete, finitely checkable subclass
inside that side.  The subclass uses the actual multi-quitter and continuer
rows, information discarded by the normalized singleton matrix.

The five-player adapter below has standard-Q cyclic normal core, is
nonpassive, fails the simpler reward-range test, has no sure-exit set, and has
no instant-no-join owner.  Thus the new producer is not merely a repackaging of
those named elementary branches.  The improvement is strict relative to the
audited named producers.  It is not a solution of all standard-Q games or of
the finite-quitting conjecture.

## Proof

Because `pi(i)` Quits with probability at least `alpha>0` throughout the
closed box,

`c_i(p)<=1-alpha<1`.

Thus every denominator `1-c_i` is positive and every `V_i` and `G_i` is
continuous on the whole box.

Reindex the gaps by

`F_j(p)=G_(pi^(-1)(j))(p)`.

The assumptions say that `F_j` is positive on the lower `j`-face and negative
on the upper `j`-face.  Fix any `lambda>0` and define the continuous self-map

`Phi_j(p)=clamp_[alpha,beta](p_j+lambda F_j(p))`.

Brouwer's fixed-point theorem gives `p*` with `Phi(p*)=p*`.  A lower-face
coordinate cannot be fixed because its increment is strictly positive, and
an upper-face coordinate cannot be fixed because its increment is strictly
negative.  Hence `p*` is interior.  There the clamp cannot conceal a nonzero
increment, so `F(p*)=0`.  Bijectivity of `pi` yields `G(p*)=0`.

Let `v=V(p*)`.  The pure-Quit endpoint is

`R_i(p*)=V_i(p*)=v_i`.

The pure-Continue endpoint, with target `v` after an all-Continue row, is

`W_i(p*)+c_i(p*)v_i=(1-c_i(p*))V_i(p*)+c_i(p*)v_i=v_i`.

Thus the row is exact endpoint Nash and its successor payoff is `v`.  Every
coordinate of `p*` is positive, so the joint all-Continue mass is below one.
For every player `i`, the opponent `pi(i)` Quits with positive probability,
so the opponents-only Continue mass is also below one.  The checked theorem
`isZeroAsymptoticNash_stationary_of_fixedPoint_endpointNash_contracts`
therefore supplies the exact terminal-Nash conclusion against arbitrary
behavioral deviations.  The checked theorem
`isUniformEquilibriumPayoff_of_stationaryEndpointCertificate_contracts`
supplies the fixed-target uniform-equilibrium-payoff conclusion.  Both are in
`UniformEquilibrium/Quitting/Stationary/EndpointCompiler.lean`.

For the range corollary, condition on the quitting set `T subset K_i`.  On the
lower blocker face the pure-Quit payoff is bounded by

`R_i(p)>=(1-alpha)H_i^-+alpha L_i^->C_i^+>=V_i(p)`.

Here `V_i` lies between `C_i^-` and `C_i^+` because it is the conditional
expectation of literal continuer rewards over nonempty opponent coalitions.
The upper face similarly gives

`R_i(p)<=(1-beta)H_i^++beta L_i^+<C_i^-<=V_i(p)`.

These are exactly the required signs.  This completes both proofs.

## Finite coefficient adapter

The direct face conditions are finite actual-data conditions, not an
existence assumption about a strategy.  They also admit a division-free
sufficient check.  Define

`N_i(p)=(1-c_i(p))R_i(p)-W_i(p)=(1-c_i(p))G_i(p)`.

The positive denominator gives `sign(N_i)=sign(G_i)`.  After fixing a blocker
face, `N_i` has degree at most two in each of the `|I|-2` background
probabilities.  Affinely rescale the face box to a unit cube and expand in the
tensor Bernstein basis of multidegree two.  There are exactly

`3^(|I|-2)`

coefficients.  Strict positivity of all lower-face coefficients and strict
negativity of all upper-face coefficients imply the required signs because
the Bernstein basis is a nonnegative partition of unity.  This test is
sufficient, not necessary.  An executable exact-arithmetic checker and its
connection to the reward table are implemented by the checked declarations
listed below.

## Exact five-player actual-data adapter

Order the players `(0,1,2,a,b)` and define

```text
M5 = [ 0 -1  2  1  1
       2  0 -1  1  1
      -1  2  0  1  1
       1  1  1  0  1
       1  1  1  1  0 ].
```

Let the blocker permutation be the five-cycle

`0 -> 1 -> 2 -> a -> b -> 0`.

On singletons set

`r5({j})_i=1+M5_(i,j)`.

For every coalition `S` of size at least two set

```text
r5(S)_i = 1    if i notin S,
           -63 if i in S and pi(i) in S,
            65 if i in S and pi(i) notin S.
```

Take `alpha=1/8` and `beta=3/4`.  Fix a player `i`, put
`q=p_(pi(i))`, and let `z` be the probability that at least one of the other
three opponents Quits.  Then

`169/512 <= z <= 63/64`

and the pure-Quit endpoint satisfies

`R_i=1+64((1-q)z-q)`.

On the lower blocker face,

`R_i-1>=64((7/8)(169/512)-1/8)=671/64`.

On the upper blocker face,

`R_i-1<=64((1/4)(63/64)-3/4)=-129/4`.

If `i` Continues, a singleton opponent coalition pays a number in `[0,3]`
and a multi-quitter opponent coalition pays `1`.  Hence

`-1<=V_i-1<=2`.

Therefore the exact face margins are

`q=1/8: G_i>=543/64>0`,

`q=3/4: G_i<=-125/4<0`.

The theorem produces an interior exact stationary equilibrium with its
endogenous target.  Proposition 9's range screen does not apply: on the lower
face its relevant crude values include

`H_i^-=1`, `L_i^-=-63`, `C_i^+=3`,

whose mixture is `-7`, not greater than `3`.

The normalized singleton matrix is exactly `M5`, since every own singleton
payoff is one.  Players `a,b` leave the first normal layer because their rows
have only positive off-diagonal entries.  Players `0,1,2` persist through
their cyclic `-1` witnesses, so the normal core is `{0,1,2}` and its principal
matrix is exactly the checked `cyclicMatrix`.  The declarations
`cyclicMatrix_standardQ` and `cyclicMatrix_noHomogeneous`
(`UniformEquilibrium/Quitting/Classification/LCP/StandardQSideExample.lean`)
give the required matrix properties after the literal adapter and reindexing
are formalized.  The literal five-player adapter and its distinguishing
regressions are checked in
`UniformEquilibrium/Diagnostics/Quitting/Regression/ConditionalFaceGapFivePlayer.lean`.

## Boundary and falsification tests

The five-player table is outside the audited named elementary producers:

- The empty sure-exit set fails because every own singleton reward is `1>0`.
  Every nonempty sure-exit set would force exact membership alternation around
  the odd blocker cycle, which is impossible.  All 32 coalitions were also
  independently cross-checked.
- For every singleton owner `o`, a nonpredecessor outsider can join for `65`
  instead of a singleton payoff at most `3`.  Thus every
  `IsQuittingInstantNoJoin r5 o` fails; the checked necessity theorem
  `isQuittingInstantNoJoin_of_works` excludes instant punishment.
- The normalized matrix is not circulant under any relabelling: its three core
  rows have off-diagonal multiset `{-1,1,1,2}`, while its two other rows have
  `{1,1,1,1}`.  It is not cardinally symmetric, not a `colliderReward`, and
  has five players rather than three.

The following failed implications were tested and retained:

- If `alpha=0`, a box corner may have `c_i=1`, so `V_i` is `0/0` and a strict
  face hypothesis cannot hold through the division-free numerator.  The
  positive lower bound is load-bearing.
- Either face sign alone is insufficient.  Passive continuer tables with all
  quitter endpoints constantly `1`, or constantly `-1`, satisfy only one
  orientation and have no gap zero.
- A shared noninjective blocker map is insufficient: two players can demand
  distinct root probabilities from the same coordinate.  The permutation
  hypothesis is load-bearing.
- Weak face signs still give a possibly boundary zero, but do not give the
  asserted interior root.  Strict signs are used exactly for interiority.
- The four-player predecessor table used during discovery has correct face
  bounds but own singleton rewards zero, so the empty coalition is already a
  sure-exit set; its alternating pairs are sure-exit sets as well.  It was
  rejected as a novelty witness rather than silently retained.

As a small positive algebra check for the range corollary, the two-player
table

`r({1})=(2,1)`, `r({2})=(1/2,3)`, `r({1,2})=(-2,-1)`

with `alpha=1/4`, `beta=3/4`, and the transposition blocker has the exact root

`p_1=1/2`, `p_2=3/8`, `v=(1/2,1)`.

This confirms that the endogenous target need not be zero.

## Probability, information, and deviation audit

The produced profile uses independent private randomization at each live date
and depends only on the fact that the game is still live.  The quitting set is
publicly observed when the game absorbs.  No public random signal is assumed.

The stationary calculations establish only the row certificate.  Coverage of
an arbitrary unilateral behavioral replacement comes from the two named
checked endpoint compilers, using joint absorption and player-deleted
contraction.  A deviator may condition on the entire observed live history and
use fresh private randomization.  The result is therefore not limited to
stationary, Markov, pure, or finite-memory deviations.

The target is one fixed vector `v=V(p*)`.  It does not depend on the accuracy
parameter in the definition of uniform-equilibrium payoff.  The stationary
profile itself is exact, so it can be reused for every accuracy; contraction
provides the sufficiently long horizon threshold.

## Source correspondence

- `quittingUniformEquilibriumPayoffConjecture`
  (`UniformEquilibrium/Quitting/Conjecture/Basic.lean`) is the open universal
  target.  This packet proves only a special actual-data class.
- `isZeroAsymptoticNash_stationary_of_fixedPoint_endpointNash_contracts` and
  `isUniformEquilibriumPayoff_of_stationaryEndpointCertificate_contracts`
  (`UniformEquilibrium/Quitting/Stationary/EndpointCompiler.lean`) are the
  checked unrestricted-behavior semantic consumers.
- `quittingStationaryFixedOpponentsQuitValue`,
  `quittingStationaryFixedOpponentsContinueReward`, and
  `quittingStationaryFixedOpponentsContinueMass`
  (`UniformEquilibrium/Quitting/Stationary/SnellCap.lean`) are the checked
  endpoint quantities corresponding to `R_i`, `W_i`, and `c_i`.
- `exists_stationaryUniformEquilibriumPayoff_or_standardQMatrixSide`
  (`UniformEquilibrium/Quitting/Classification/LCP/StationaryExistence.lean`)
  stops on the standard-Q alternative and supplies no strategy there.
- `IsQuittingSureExitSet`, `isQuittingSureExitSet_empty_iff`, and
  `isUniformEquilibriumPayoff_setReward_of_isQuittingSureExitSet`
  (`UniformEquilibrium/Quitting/Paths/SureExitSet.lean`) are the audited pure
  branch and exposed the rejected four-player overlap.
- `isQuittingInstantNoJoin_of_works`
  (`UniformEquilibrium/Quitting/Punishment/InstantPunishment.lean`) is the
  audited necessary condition for the instant-punishment branch.
- `quittingGame_exists_uniformEquilibriumPayoff_of_cardinalSymmetric`
  (`UniformEquilibrium/Quitting/Classification/SymmetricQuittingGame.lean`),
  `exists_uniformEquilibriumPayoff_of_circulant_surplus_nonpos`
  (`UniformEquilibrium/Quitting/Classification/Circulant/Trichotomy.lean`),
  the definition of `colliderReward`
  (`UniformEquilibrium/Quitting/Classification/Circulant/ColliderCompletion.lean`),
  and `quittingGame_exists_uniformEquilibriumPayoff_threePlayer`
  (`UniformEquilibrium/Quitting/Classification/ThreePlayer/Existence.lean`)
  are the other named positive classes excluded by the exact adapter audit.
- Section 5.1 of the Solan--Solan quitting-game source, faithfully transcribed
  in `Literature/SolanAndSolan2020.lean`, gives `theorem5_1_nonQ` on the non-Q
  side; its Q-side statement uses a public signal.  The present theorem is a
  private-independent exact stationary producer only for the displayed
  multi-quitter subclass.  It does not remove the public signal in general.

A narrow search for `conditional continuer`, `blocker face`,
`Poincare--Miranda`, and `Bernstein coefficient` found no existing source
theorem with this actual reward-table criterion.  Novelty is asserted only
relative to the named audited sources, not absolutely against every possible
conditional theorem.

## Checked Lean realization

`exists_stationaryCertificate_of_conditionalFaceGap`,
`exists_stationaryTerminalNash_of_conditionalFaceGap`, and
`exists_uniformEquilibriumPayoff_of_conditionalFaceGap`
(`UniformEquilibrium/Quitting/Classification/Existence/ConditionalFaceGap.lean`)
implement the raw face-gap adapter and its exact stationary terminal-Nash and
unrestricted-behavior uniform-payoff consumers.  The finite reward-range
variant is checked in `ConditionalFaceGapRange.lean`.  The literal five-player
actual-data instance and its nonpassive/range-failure regressions are checked
by `exists_uniformEquilibriumPayoff` and
`not_isQuittingConditionalFaceGapRange`
(`UniformEquilibrium/Diagnostics/Quitting/Regression/ConditionalFaceGapFivePlayer.lean`).

## Scope and nonclaims

- The general theorem, literal actual-data adapter, and semantic consumer are
  proved in Lean.  The optional Bernstein-coefficient checker described in the
  source notebook is not part of the checked realization.
- It does not prove the finite-quitting uniform-equilibrium conjecture, solve
  every standard-Q game, or classify all conditional face-gap tables.
- It does not claim that the face signs are necessary.
- It does not use or export the later weak-sign, nonbijective, linear-mixing,
  or arbitrary-completion extensions from the source notebook.
- It makes no claim about arbitrary finite stochastic games beyond the
  quitting-game model.
