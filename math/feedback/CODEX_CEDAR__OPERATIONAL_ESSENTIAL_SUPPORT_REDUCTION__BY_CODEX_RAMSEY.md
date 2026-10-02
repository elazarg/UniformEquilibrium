# Review of `OPERATIONAL_ESSENTIAL_SUPPORT_REDUCTION`

Reviewer: `CODEX_RAMSEY`

Verdict: **PASS in the stated local quiet-lift scope.**  Propositions 1--3,
their constants, and their arbitrary-behavior semantics check.  The genuinely
new operational content is narrow: after the deleted player is localized, a
finite deterministic quit time retains the exact gain `gamma`.  The result
does not co-realize witnesses across different deletion blocks and does not
add a chronological or equilibrium-lifting conclusion.  The amended
stopping-law support-atom extraction also passes.

## Claim audited

For a block `B`, lift a terminal `epsilon`-Nash profile of the block-deleted
game by making every deleted player play literal Never.  If the ambient table
has terminal exploitability gap `gamma` and `epsilon<gamma`, Proposition 1
claims that an ambient gap witness must belong to `B`.  Proposition 2 claims
that, when `gamma>0`, the same deleted player can be replaced by quitting at
some finite deterministic time while retaining the full gain `gamma`.
Proposition 3 uses cardinal minimality to produce the survivor approximate
equilibrium for every nonempty proper block.

## Independent check

### Proposition 1: exact outsider localization

Apply `HasTerminalExploitabilityGap` to the literal quiet lift.  It returns an
ambient player `d`, an arbitrary behavioral deviation `tau`, and the claimed
gain `gamma`.

If `d` survives, the two checked identities in
`PlayerDeletionLift.lean` have exactly the direction used in the note:

```text
quittingTerminalPayoff_liftDeletedProfile
quittingTerminalPayoff_update_liftDeletedProfile_eq_deleteDeviation
```

The first identifies the prescribed survivor payoff before and after the
lift.  The second transports the payoff of the arbitrary ambient deviation to
`quittingDeletedDeviation` in the survivor game, with no error and no
stationarity restriction.  The survivor `epsilon`-Nash inequality then gives
`gamma<=epsilon`, contradicting `epsilon<gamma`.  Hence `d in B`.

Taking the unrestricted best-reply supremum immediately gives best-reply debt
at least `gamma` at this same quiet-lift source.  No off-path behavior is lost:
the transport theorem itself accepts an arbitrary behavioral strategy and
uses the quitting game's unique live history.

### Proposition 2: exact finite deterministic provenance

For the particular behavioral deviation `tau` returned by Proposition 1,
the checked identity

```text
quittingTerminalPayoff_update_eq_expect_stoppingLaw_pureTime
```

expresses its payoff exactly as the expectation, under
`quittingBehaviorStoppingLaw reward tau`, of the deterministic finite-Quit
and Never payoffs.

Suppose every finite Quit time paid strictly less than the source payoff plus
`gamma`.  Since `d in B`, the quiet lift already makes `d` play Never, and

```text
Function.update_liftDeletedProfile_never
```

shows that the Never atom pays exactly the source payoff, also strictly below
the threshold because `gamma>0`.  Thus every atom value is below the
threshold.

Strictness is not lost in the countable expectation.  The stopping law is a
PMF and hence has a positive-mass support atom.  All threshold deficits are
nonnegative and the chosen support atom has both positive real mass and
strictly positive deficit.  Payoff boundedness gives absolute summability,
while `quittingHazardStoppingLaw_toReal_tsum_one` gives total real mass one.
Consequently the expected value is strictly below the threshold, contradicting
Proposition 1 and the exact disintegration.  Some finite time therefore pays
at least source plus the full `gamma`.

This proof does not infer attainment from an `sSup`.  It extracts an atom from
the stopping law of the particular gap-witnessing strategy; the positive
support mass is exactly what preserves the strict inequality.

### Proposition 3: cardinal-minimal producer

If `B` is nonempty and proper, the survivor subtype is nonempty and

```text
card (QuittingBlockSurvivor B)
  = minimal.playerCount - B.card
  < minimal.playerCount.
```

The strict inequality uses `B.Nonempty`; survivor nonemptiness uses
`B != univ`.  Thus

```text
MinimalFinQuittingCounterexample.exists_uniformEquilibriumPayoff_of_card_lt
```

applies directly to the block-native deleted table.  The checked terminal
selection theorem supplies a terminal `(gamma/2)`-Nash profile because
`gamma>0`.  Proposition 2 gives the full gain `gamma` at a finite quit time.
For an arbitrary prescribed `0<epsilon<gamma`, Proposition 1 gives the
ambient behavioral gap `gamma` exactly as claimed.

No reindexing between restriction and deletion subtypes is used.

## Novelty and subsumption boundary

The note's novelty qualification is accurate.

- `exists_mem_gap_le_blockDeletionExcessBound_or_survivorGap` already contains
  the same deleted-versus-survivor split in stronger quantitative excess-bound
  form under a per-stage absorption hypothesis.
- `exists_mem_gap_le_blockDeletionExcessBound` kills the survivor arm using
  the same strict error comparison, again under that hypothesis.
- Proposition 1 avoids the absorption-bound hypothesis only because it keeps
  the original ambient deviation rather than producing the checked finite
  excess estimate.  Numerically it is a direct localization argument, not a
  new deletion inequality.
- `QuittingTerminalExploitabilityWitness.exists_pureTimeCap_gap` already puts
  the full gap below the pure-time supremum at an arbitrary profile.  It does
  not select an attaining finite time or retain the identity of a player
  previously localized to `B`.  Proposition 2's exact stopping-law
  disintegration and positive-support-atom argument are therefore the
  genuinely additional executable provenance.

A narrow search found no existing declaration returning, from a block-deleted
survivor approximate equilibrium, the same deleted player together with a
finite deterministic quit time and the displayed exact `gamma` bound.

## Co-realization audit and relation to the Fin4 handoff

There is no overstated cross-block co-realization claim.  For one fixed
`B,sigma`, the quiet lift, deleted player, and finite-time deviation are
co-realized at one actual ambient profile.  The note explicitly says that
`sigma`, `d`, and `t` may all change when `B` changes, and that adjoining the
returned player is only a finite set-growth algorithm with complete
reselection—not behavioral chronology.

The result does not close or conflict with the reviewed Fin4 prescribed-owner
stationary handoff:

- At the singleton-base source `sigma_t` of that handoff, the owner Quits
  surely, so the source is not the quiet lift obtained by deleting that owner.
- At the repaired profile `tau_t`, the old owner does play Never, but the
  co-realized next debtor has unrestricted debt at least the terminal gap.
  Hence the surviving profile obtained by deleting only the old owner is not
  an `epsilon`-Nash profile for `epsilon<gamma`, which is the hypothesis needed
  by Proposition 1.
- More generally, Proposition 3 may re-solve a proper survivor game, but it
  provides no equality with `tau_t`, no preservation of the handoff's paid
  row or terminal law, and no successor relation to the next singleton-base
  source.

Indeed the Fin4 repaired profile already carries a stronger local operational
witness: a source-matched paid first-disagreement row with full gap for its
returned outside debtor.  The unresolved Fin4 datum is a connector from that
repaired profile to the next reselected source, not another finite quit-time
passport.  Thus the deletion theorem is absorbed at the local-deviation level
but remains independent as a cardinal-minimal proper-subsystem producer.

## Boundary checks

1. At `epsilon=gamma`, the contradiction in Proposition 1 disappears.
2. The hypothesis `gamma>0` is essential: it makes the Never value strictly
   smaller than the target threshold.
3. If `B` is empty, a deleted witness cannot exist; the hypotheses force the
   survivor contradiction instead.  If `B=univ`, Proposition 3 has no
   nonempty survivor type.  Both endpoints are correctly excluded there.
4. The exact finite-time conclusion depends on the stopping-law mixture of the
   particular witness, not on an abstract pure-time supremum.
5. The lift result proves an actual source/deviation statement but no positive
   reach after the chosen time, coalition-incidence label, Bellman edge,
   punishment-floor safety, or near-return.

## Sources inspected

- `UniformEquilibrium/Quitting/Classification/PlayerDeletionLift.lean`;
- `UniformEquilibrium/Quitting/Classification/BlockDeletion.lean`;
- `UniformEquilibrium/Quitting/Classification/BlockDeletionInequality.lean`;
- `UniformEquilibrium/Quitting/Cycles/BehaviorPureTimeExtremality.lean`;
- `UniformEquilibrium/Quitting/Cycles/TerminalExploitabilityPeriodicProfile.lean`;
- `UniformEquilibrium/Quitting/Paths/BehaviorStoppingLaw.lean`;
- `UniformEquilibrium/Quitting/Paths/BehaviorStoppingPayoff.lean`;
- `UniformEquilibrium/Diagnostics/Quitting/MinimalFinCounterexample.lean`;
- `UniformEquilibrium/Quitting/Terminal/ExploitabilityGap.lean`;
- `UniformEquilibrium/Quitting/Terminal/TargetTail/TerminalUniformPayoffSelection.lean`.

No external paper result is used.
