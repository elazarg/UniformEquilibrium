# Fin4 singleton-base same-law reset producer

Author: `CODEX_EULER`

Independent reviews:

- [`CODEX_RAMSEY`](../feedback/CODEX_EULER__FIN4_CODIMENSION_ONE_PASSPORT_PAIRBASE_ALIGNMENT__BY_CODEX_RAMSEY.md)
- [`CODEX_MINER`](../feedback/CODEX_EULER__FIN4_CODIMENSION_ONE_PASSPORT_PAIRBASE_ALIGNMENT__BY_CODEX_MINER.md)

Source note:
[`CODEX_EULER__FIN4_CODIMENSION_ONE_PASSPORT_PAIRBASE_ALIGNMENT.md`](../notes/CODEX_EULER__FIN4_CODIMENSION_ONE_PASSPORT_PAIRBASE_ALIGNMENT.md),
Theorem 4.2 and Corollary 4.3 only.  The later Section 10 carrier-descent
proposal is not part of this packet.

## Exact statement

Let the player type be literally `Fin 4`, and let

```text
reward : {S : Finset (Fin 4) // S.Nonempty} -> Payoff (Fin 4)
```

be a quitting reward table.  Fix `M>=0` such that

```text
|reward(S)_i|<=M                                     (1.1)
```

for every nonempty quitting coalition `S` and player `i`.  Suppose that the
same table carries

```text
residual : FinFourQuantitativeFullSupportHardResidual reward M.
```

Write

```text
witness=residual.witness,
Gamma=witness.terminalGap>0.
```

For every prescribed player `j`, there are:

* a distinct player `d`;
* an induced mixed-Nash point `z` on the three free labels
  `F=univ.erase j`;
* the persistent singleton-base root

  ```text
  q=quittingPersistentBaseRoot {j} F z,
  ```

  in which `j` Quits surely;
* its literal stationary behavioral profile `sigma`;
* its terminal-semantic pair and complete terminal-outcome law

  ```text
  T=quittingTerminalSemanticPair reward sigma,
  mu=quittingTerminalOutcomeMass reward sigma;
  ```

* a positive global minimum `X_*` of total terminal-semantic debt; and
* a returned terminal-semantic pair `R`;

such that all of the following hold.

### A. Three solved free coordinates

For every `i in F`, the prescribed payoff equals the unrestricted behavioral
stationary cap and lies above the punishment value:

```text
T.1_i=quittingStationaryUnilateralCap reward q i,
quittingPunishmentValue reward i<=T.1_i.             (1.2)
```

Equivalently, every free coordinate has terminal-semantic debt zero:

```text
d_i(T)=0.                                            (1.3)
```

In particular `d_d(T)=0`.

### B. One debtor and a source-matched paid row

The unique possible positive-debt coordinate is the sure base owner `j`, and
it has the full terminal gap:

```text
d_j(T)>=Gamma,
{i:d_i(T)>0}={j}.                                    (1.4)
```

On this same literal stationary profile, two deterministic pure stopping
times of player `j`, including `Never` when selected, differ by at least
`Gamma`.  The checked first-disagreement decoder therefore yields

```text
QuittingPaidFirstDisagreementRow reward sigma j Gamma. (1.5)
```

The paid row is source matched to `sigma`; it is not inferred merely from the
semantic pair.

### C. Quantitative strict-superset terminal mass

Let `A_free` be the probability that at least one of the three free players
Quits in the date-zero row.  Then `M>0` and

```text
A_free>=Gamma/(Gamma+2M).                             (1.6)
```

Consequently there is a nonempty `K subset F` such that the prescribed
terminal coalition `{j} union K` satisfies

```text
mu(some ({j} union K))>=Gamma/[7(Gamma+2M)].          (1.7)
```

Thus the strict-superset atom belongs to the actual complete law of the same
stationary source.

### D. The same law enters the fixed-law reset dispatcher

The stationary pair/law is an actual point of the joint carrier,

```text
(T,mu) in quittingTerminalSemanticLawCarrier reward. (1.8)
```

Every prescribed terminal coalition contains `j`, and `j!=d`.  Hence the
opponent-incidence coordinate is exactly one:

```text
quittingTerminalOpponentIncidenceMass d j mu=1.      (1.9)
```

The source `X_*` lies in the terminal-semantic carrier, globally minimizes
total debt there, and has positive total debt.  The returned point `R`
satisfies

```text
QuittingFixedLawResetDispatch
  (reward:=reward) X_* T mu d j R.                    (1.10)
```

In particular, the checked dispatcher retains this complete law and gives
its inclusive dynamic alternative:

1. an exact positive-absorption, positive-survival cap-Nash root whose
   semantic prefix strictly lowers debt at `R` and whose prefixed law retains
   positive `(d,j)` incidence; or
2. the exact all-Continue cap-face fixed point at `R`.

The theorem does not assert that the first arm occurs.

## Conjecture-facing change

The maintained question
[`FOUR_PLAYER_SINGLETON_PACKET_DISPATCH.md`](../questions/FOUR_PLAYER_SINGLETON_PACKET_DISPATCH.md)
requires partial work to use actual hard-residual data and either enter an
established semantic consumer, close a named subchamber, or decrease a
declared rank.  Before this result, the checked full-gap collision at every
singleton and the checked persistent-base/reset modules were separate
interfaces.  An arbitrary prescribed singleton owner was not packaged with
all of the following on one selected source:

```text
actual hard residual
  -> full-gap singleton collision (j,d)
  -> actual singleton-base stationary Nash source
  -> unique debtor j + three solved free coordinates
  -> quantitative strict-superset atom + paid row
  -> zero-debt reset owner d with unit incidence
  -> fixed-law reset dispatch on the same pair and law.
```

This packet supplies that arrow for every `j`.  It therefore enters the named
checked fixed-law reset consumer without reselecting its target law and
strictly strengthens the prescribed-owner stationary handoff.  It does not
eliminate the dispatcher's all-Continue arm and does not prove the Fin4
conjecture.

The reviewed source note also contains pair-base and codimension-one passport
reductions.  They are omitted here because the unconditional hard-residual
singleton-base statement is the narrowest source-to-consumer producer.

## Definitions and assumptions

### Probability and profile

At every live date the players' Quit/Continue actions are independently
randomized according to their product root.  The persistent singleton-base
root makes `j` Quit with probability one and gives the other three players
the mixed actions selected by the finite induced Nash point `z`.  Its
stationary profile repeats the same row, although absorption already occurs
at date zero because `j` Quits surely.

All nonempty date-zero coalitions, including simultaneous quits, use their
literal `reward` row.  The complete law `mu` also includes the Never outcome,
whose mass here is zero.

### Observation and unilateral agency

The game's behavioral strategies may depend on the entire observed finite
history and use fresh private randomization.  A unilateral deviator may
replace its whole behavioral strategy and may choose arbitrary stopping-time
behavior, including Never.  There is no public correlation device and no
restriction to stationary, one-shot, deterministic, or bounded-memory
deviations.

The three free players nevertheless reduce exactly to the induced one-stage
binary game: the nondeviating sure base owner `j` ends play at date zero under
every unilateral replacement by a free player.  Thus their induced Nash
inequalities are their full unrestricted behavioral-cap inequalities.  The
base owner's positive debt is decoded through the checked pure-time
extremality and first-disagreement interfaces, not through stationary regret.

### Semantic pair, debt, and law

For a behavioral profile `sigma`, its terminal-semantic pair is

```text
T=(U,B),
U_i=prescribed terminal payoff,
B_i=supremum over all unilateral behavioral replacements by i.
```

Debt is `d_i(T)=B_i-U_i`, and total debt is `D(T)=sum_i d_i(T)`.  A
terminal-semantic carrier point may generally be a compact limit, but the
target `T` and law `mu` in this theorem come from the literal stationary
profile `sigma`.

The reset source `X_*` is a compact carrier minimum.  The returned reset pair
need not be the semantic pair of one attained profile; the checked fixed-law
dispatcher is stated at the carrier level.

## Source correspondence

No paper theorem is used.  The argument is a new composition and quantitative
singleton-base calculation over current production declarations.

### Actual hard-residual source

The structure
`FinFourQuantitativeFullSupportHardResidual` and the unconditional alternative

```text
uniformPayoff_or_nonempty_finFourQuantitativeFullSupportHardResidual
```

are in
`UniformEquilibrium/Diagnostics/Quitting/Collision/SingletonPacket/FullSupportProjectiveQBarResidual.lean`.
The residual retains the terminal witness, quantitative full-support packet,
full normal core, punishment normality, and nonprojective hard LCP class on
one table.

For every singleton owner, the checked theorem

```text
FinFourQuantitativeFullSupportHardResidual.
  exists_terminalGap_collision_at_singleton
```

in
`UniformEquilibrium/Diagnostics/Quitting/Collision/SingletonPacket/PunishmentNormalAtomicCollisionHandoff.lean`
supplies `d!=j` with

```text
reward({j})_d+Gamma<=reward({j,d})_d.                 (3.1)
```

This is the actual-data adapter used here.

### Stationary source components

The induced game, compact mixed-Nash set, persistent-base root, and
nonemptiness theorem

```text
quittingPersistentBaseNashSet_nonempty
```

are in
`UniformEquilibrium/Diagnostics/Quitting/Collision/Toggles/PersistentBaseInducedGame.lean`.
The full behavioral-cap and punishment-floor meaning of a free induced-Nash
coordinate is checked by

```text
persistentBase_inducedNash_free_semantics
```

in
`UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticFinFourSoloWallDispatch.lean`.

The stationary cap/pure-time bridge and paid-row endpoint are checked by

```text
quittingTerminalSemanticPair_stationary_envelope_eq_cap
exists_oriented_quitNow_never_gap_of_stationary_cap_debt
exists_quittingPaidFirstDisagreementRow_of_pureTimePayoff_sub.
```

They live respectively in
`TerminalSemanticNegativeVertexGerm.lean`,
`LargeBaseStationarySemanticHandoff.lean`, and
`TerminalSemanticPaidFirstDisagreement.lean` under the diagnostics subtree.

### Reset consumer

The joint semantic/law carrier, opponent incidence, structure
`QuittingFixedLawResetDispatch`, and theorem

```text
QuittingTerminalExploitabilityWitness.exists_fixedLawResetDispatch
```

are checked in
`UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticResetIncidenceCapReturn.lean`.
The positive global minimum used as its source is supplied from absence of a
uniform payoff by

```text
exists_positive_minimumTerminalSemanticDebt_face_of_no_uniformPayoff
```

in
`UniformEquilibrium/Quitting/Root/TerminalSemanticEqualityStratum.lean`.
The terminal witness implies the required absence of a uniform-equilibrium
payoff.

### Novelty audit

Narrow searches found older checked wrappers for prescribed-owner stationary
handoffs and fixed-law resets, including the packet recorded in
[`FIN4_PRESCRIBED_OWNER_LABEL_HANDOFF_ALIGNMENT.md`](../formalized/FIN4_PRESCRIBED_OWNER_LABEL_HANDOFF_ALIGNMENT.md).
Those wrappers do not combine the collision-selected distinct reset owner
with this exact singleton-base target's unique debtor, quantitative
strict-superset atom, paid row, and unchanged complete law.  No checked
declaration was found for the composition (1.2)--(1.10).

## Proof

Fix the prescribed owner `j`.  The hard-residual collision theorem selects
`d!=j` satisfying (3.1).  Put `F=univ.erase j`.  Choose

```text
z in quittingPersistentBaseNashSet reward {j} F
```

using its checked nonemptiness theorem, and form the corresponding root `q`,
stationary profile `sigma`, pair `T`, and law `mu`.

### 1. Free-player semantics

The base `{j}` is nonempty and disjoint from `F`.  Since `j` Quits surely,
absorption occurs at date zero even after any one free player replaces its
entire behavioral strategy.  Apply
`persistentBase_inducedNash_free_semantics`.  This proves (1.2) for every
free player and therefore (1.3), including `d_d(T)=0`.

### 2. Quantitative free absorption

Write the free Quit probabilities as `x_d,x_k,x_l`, where `k,l` are the two
free labels other than `d`, and put

```text
z0=(1-x_k)(1-x_l).
```

If `x_d=1`, then `A_free=1` and (1.6) is immediate.  Suppose `x_d<1`.
Continue then has positive probability in `d`'s mixed Nash action, so its
expected Quit-minus-Continue endpoint difference is nonpositive.

Conditional on both `k` and `l` Continuing, (3.1) makes that endpoint
difference at least `Gamma`.  At every other pure `k,l` corner it is bounded
below by `-2M`, since it is the difference of two terminal reward coordinates
in `[-M,M]`.  Therefore

```text
0>=z0*Gamma-(1-z0)*2M,
1-z0>=Gamma/(Gamma+2M).                               (4.1)
```

The event that `k` or `l` Quits is contained in free absorption, so (4.1)
proves (1.6).  The positive terminal gap and (1.1) also imply `M>0`.

Because `j` Quits surely, the seven nonempty subsets `K` of the three-player
free set are exactly the possible terminal coalitions strictly containing
`{j}`.  Their masses sum to `A_free`.  Pigeonhole and (1.6) give (1.7).

### 3. Unique debt and paid first disagreement

Every free debt is zero.  The terminal witness says that the unrestricted
terminal exploitability of the literal profile `sigma` is at least `Gamma`,
so one coordinate of its semantic pair has debt at least `Gamma`.  The only
remaining coordinate is `j`, proving `d_j(T)>=Gamma`.  Semantic debts are
nonnegative, hence their positive support is exactly `{j}`.

For a stationary product profile the checked cap theorem identifies the
unrestricted cap with the better of immediate Quit and Never, while the
prescribed payoff lies between those two endpoints.  The oriented gap theorem
therefore selects one direction between the two pure-time payoffs with gain at
least `Gamma`.  Feed that exact orientation to
`exists_quittingPaidFirstDisagreementRow_of_pureTimePayoff_sub`.  This proves
(1.5) on the same literal `sigma`, retaining finite times and Never exactly.

### 4. Same-law reset dispatch

Literal profile semantics give joint-carrier membership (1.8).  Every
terminal realization under `sigma` contains `j`, and `j!=d`; the Never mass is
zero.  Expanding the definition of opponent incidence therefore gives the
exact identity (1.9).

The terminal witness excludes a uniform-equilibrium payoff.  Apply
`exists_positive_minimumTerminalSemanticDebt_face_of_no_uniformPayoff` and
choose its carrier minimum `X_*`.  Its total debt is positive because it has a
positive debt coordinate.

Now apply `witness.exists_fixedLawResetDispatch` with source `X_*`, target
`T`, mass `mu`, reset owner `d`, and incidence label `j`.  Global minimality
and positivity come from `X_*`; (1.8), `d_d(T)=0`, and (1.9) are the other
hypotheses.  Its returned pair `R` satisfies (1.10), including exactly the
two inclusive dynamic arms stated above.  QED.

## Boundary tests

1. **Free player surely Quits.**  If `x_d=1`, no Continue-support inequality
   for `d` is used; free absorption is already one.  The proof splits this
   case before applying the mixed-support sign.

2. **Other free players never Quit.**  If `x_k=x_l=0` and `x_d<1`, then
   `z0=1` and (4.1) would give `0>=Gamma`, impossible.  Thus the collision
   premium really forces positive strict-superset mass.

3. **Boundary mixed actions.**  The induced Nash point may lie on any face of
   its polytope.  Sure base absorption still makes every free unilateral
   deviation a date-zero membership decision, so no interiority assumption is
   hidden in (1.2).

4. **Paid-edge orientation.**  The gap may be Quit-now over Never or Never
   over Quit-now.  The paid-row decoder accepts both after choosing source and
   receiving witnesses in the corresponding order.  The theorem does not
   force one orientation.

5. **All-Continue reset wall.**  The checked regression
   `positive_incidence_and_toggle_but_only_allContinue_capNash` has unit
   incidence and a strict supported toggle while only the all-Continue cap
   root is available.  It is not a hard-residual counterexample, but it proves
   that the retained local fields cannot delete the second reset arm.

6. **Target versus returned pair.**  The fixed-law reset dispatcher keeps
   `mu` but may change the semantic pair from `T` to `R`.  No equality
   `R=T` is used or claimed.

## Adapter and consumer

The adapter is unconditional on the hard-residual branch.  Given
`residual` and any requested `j`, the named collision theorem selects `d`;
finite mixed-Nash existence selects `z`; literal stationary semantics select
`T,mu`; and the terminal witness supplies `X_*`.  No hard principal, marked
lasso, arbitrary certificate, or separately selected law is assumed.

The consumer is the checked `exists_fixedLawResetDispatch`.  The packet's new
work proves that its target/reset/incidence hypotheses are co-realized by the
same actual singleton-base pair and law while retaining the unique debtor,
paid row, and atom.  The consumer returns either strict semantic debt descent
at its returned point or the exact all-Continue cap-face obstruction.  It is
not itself a uniform-payoff consumer.

## Checked Lean realization

The result is proved in
`UniformEquilibrium/Diagnostics/Quitting/Collision/SingletonPacket/SingletonBaseSameLawResetProducer.lean`.
The structure `FinFourSingletonBaseSameLawResetProducer` stores the selected
reset owner, actual induced Nash point and stationary source, all three solved
free coordinates, the unique full-gap debtor and source-matched paid row, the
quantitative free-absorption and seven-atom bounds, joint-carrier membership,
unit incidence, the positive global minimum, and the same-law fixed-reset
dispatch.  The source-facing capstone is
`FinFourQuantitativeFullSupportHardResidual.nonempty_singletonBaseSameLawResetProducer`.

The declaration has `M`, `L`, and `A`.  It has `C` into the checked
`QuittingFixedLawResetDispatch` interface on the same literal pair and law;
that consumer is not a uniform-payoff or near-return consumer.  Direct and
named builds, the Diagnostics umbrella build, axiom inspection, duplicate and
telescope checks, and the source/agency audit passed.  The only transitive
axioms are `propext`, `Classical.choice`, and `Quot.sound`.

## Scope and nonclaims

* The player type is literally `Fin 4`; no reindexing theorem is claimed.
* The reset owner `d` is selected by the full-gap singleton collision theorem;
  it is not prescribed independently of `j`.
* The half-gap quantitative atom from the codimension-one quiet-lift theorem
  is not used and is not identified with the stationary atom in this packet.
* The returned reset pair is not the stationary target pair, although the
  complete law is retained.
* The reset dispatcher's all-Continue arm remains open.
* The strict debt arm is local to the returned point and is not an iterable
  well-founded descent without a regeneration theorem.
* No chronological connection to another selected hard-principal, lasso, or
  paid-cap source is proved.
* No payoff near-return, terminal approximate Nash profile, uniform-
  equilibrium payoff, or proof of the Fin4 conjecture is claimed.
* The unreviewed Section 10 solo-carrier descent from the source notebook is
  deliberately excluded.
