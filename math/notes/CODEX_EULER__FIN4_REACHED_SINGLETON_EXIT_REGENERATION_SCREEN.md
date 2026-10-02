# Fin4 reached singleton exit: finite collision regeneration and its exact sign wall

**Owner:** `CODEX_EULER`  
**Status:** proved ordinary-mathematical restart repair; no conjecture consumer

## 1. Question and conclusion

The finite common-stage restart in
[`CODEX_MINER__MACROSCOPIC_REACHED_GAIN_COMMON_STAGE_RESTART_BOUNDARY`](CODEX_MINER__MACROSCOPIC_REACHED_GAIN_COMMON_STAGE_RESTART_BOUNDARY.md)
can erase one member of a marked pair and land on a positive singleton
cylinder.  This note asks whether that exit can be turned, on the same actual
source, into a prescribed-payoff charged edge, near-return, or maintained
rank descent.

There are two distinct answers.

1. **The singleton is not a terminal provenance obstruction at finite
   depth.**  At the literal reached row one can insert an arbitrarily small
   outsider Quit probability.  This preserves the actual suffix, creates a
   positive overlapping-pair cylinder, and changes the complete semantic
   pair by an arbitrarily small amount.  Thus any prescribed finite number
   of applications of the macroscopic collision dispatch can be continued
   through singleton exits, after spending an arbitrarily small additional
   near-minimum budget.
2. **The insertion is not a charged edge.**  Punishment normality supplies a
   full-gap singleton joiner, but the expected endpoint sign also sees every
   other opponent coalition at the reached product root.  The joiner's
   insertion is profitable only under an additional quantitative dominance
   condition.  The current Fin4 hard residual does not imply that condition,
   and the checked/local cross-mass regression shows it is independent of the
   advertised singleton edge.

Consequently the singleton arm is consumed for finite literal-source
regeneration, but not for the conjecture: the regenerated source returns to
the already known fixed-tail endpoint-improvement-cycle wall.  It is not an
exact Nash--Bellman edge, a floor path, or a well-founded descent.

## 2. Exact reached data

Fix a Fin4 reward table bounded by `M`, a positive terminal gap `Gamma`, and
an actual profile `sigma`.  At a reached date `t`, suppose the live root `q`
has

```text
rootCoalitionMass q {o} = m > 0.                       (2.1)
```

Write `T` for the literal suffix after `t`.  This is exactly the target
returned when a marked pair `{o,i}` is routed through the pure-Continue
endpoint of `i` in the reviewed restart theorem.  In particular the full
profile, root, suffix, semantic pair, and positive unconditional singleton
atom are all co-realized.

For `c != o` and `0 < lambda < 1`, let

```text
q^lambda = update q c ((1-lambda) q_c + lambda delta_Q),
sigma^lambda = RootThenContinuation(q^lambda,T).       (2.2)
```

If the original source came from a later reached date, prepend its unchanged
finite history.  This does not affect any calculation below.

## 3. Finite collision regeneration

### Lemma 3.1 (literal small activation)

For every `xi>0`, one can choose `0<lambda<1` such that:

1. `sigma^lambda` is an actual behavioral profile and has exactly the same
   suffix `T`;
2. its reached pair mass satisfies

   ```text
   rootCoalitionMass q^lambda {o,c} >= lambda*m > 0;   (3.1)
   ```

3. its complete terminal-semantic pair is within `xi` of that of `sigma`
   in every coordinate, hence in particular

   ```text
   |D(Sem(sigma^lambda))-D(Sem(sigma))| < 8 xi         (3.2)
   ```

   when `xi` is the coordinatewise bound on the eight Fin4 semantic
   coordinates.

#### Proof

The first-stage splice identity is the same one used in
`quittingRootThenContinuation_partialEndpoint_eq_updateSelf` in
`TerminalSemanticPlateauPartialResetTransfer.lean`.  Product independence
gives (3.1) exactly: on the old singleton event all players other than `c`
already have the required actions, and the new `c` marginal Quits with
probability at least `lambda`.

Terminal payoffs are affine in the altered one-stage marginal.  Each
unrestricted cap is a supremum over deviations of payoff functions with the
same uniform `O(lambda)` coupling bound, so it is Lipschitz as well.  Thus the
full semantic pair converges to `Sem(sigma)` as `lambda -> 0`; finite
coordinate summation gives (3.2). `QED`

The factor `8` is only bookkeeping and is not used as a sharp constant.

### Corollary 3.2 (no singleton stop at any prescribed finite depth)

Fix a finite depth `K` and a positive error reserve `zeta`.  In the finite
restart theorem, whenever a gain edge routes its marked pair to a singleton,
apply Lemma 3.1 with semantic-debt change below `zeta/K`, then invoke the
collision dispatch on the regenerated pair.  After at most `K` such
activations, the total extra near-minimum budget is below `zeta`.

Thus, for every fixed `K`, the reached-singleton alternative can be removed
from the finite-depth restart statement.  What remains is a common-tail
excursion, an actual endpoint excursion, or `K` literal profitable endpoint
repairs separated by at most `K` arbitrarily small, source-matched activation
steps.

This does **not** preserve the finite `3^4` root alphabet used for the exact
pigeonhole return: the small activation rates are new root values.  Even if
one fixes finitely many rates in advance, the activation steps have no
strategic sign, so a repeated root word is not a cycle of profitable edges.

## 4. Punishment normality removes the negative moat, not the sign wall

For the maintained Fin4 hard residual every player is punishment-normal.
The checked theorem
`FinFourQuantitativeFullSupportHardResidual.exists_terminalGap_collision_at_singleton`
therefore chooses `c != o` with

```text
r_c({o}) + Gamma <= r_c({o,c}).                        (4.1)
```

Equivalently, in
`QuittingTerminalExploitabilityWitness.negativeMoat_or_positive_pairReplacement`
the negative punishment-moat arm contradicts
`punishmentValue(o) <= r_o({o})`.  Hence a positive reached singleton always
has a full-gap static overlapping-pair replacement in the hard residual.

This still does not sign the actual insertion.  Let `w` be the probability,
under the opponents of `c` at the reached root, that their Quit coalition is
exactly `{o}`.  The expected Quit-minus-Continue endpoint difference of `c`
obeys only

```text
G_c >= w*Gamma - (1-w)*2M
    = (Gamma+2M)w - 2M.                                (4.2)
```

Thus the hard data force `G_c>0` only when

```text
w > 2M/(Gamma+2M).                                    (4.3)
```

The lower bound on the unconditional singleton atom gives no such
conditional dominance: it may be arbitrarily small, and the other rows can
make the inequality in (4.2) sharp.  Changing `c` by a smaller `lambda` does
not alter this sign; it merely multiplies the resulting gain or loss by
`lambda`.

This is precisely the content of Theorem 2.1 and the two-completion
regression in
[`CODEX_RAMSEY__STRICT_TOGGLE_SOFT_BELLMAN_CROSS_MASS_BARRIER`](CODEX_RAMSEY__STRICT_TOGGLE_SOFT_BELLMAN_CROSS_MASS_BARRIER.md): two tables can agree on the entire strict singleton edge, its gap, tail, and
pure-set caps, while one admits a charged exact soft root and the other makes
the unavoidable cross atom equal to the Nash regret.

## 5. Why the standard Fin4 consumers do not close this

* The checked pair-dropout consumer returns either the now-impossible
  punishment moat or the static pair replacement (4.1).  It explicitly does
  not claim that replacement is Nash, Bellman, or chronological.
* The singleton complementary-debt estimate
  `singletonMass_mul_otherDebt_le_tailExcess_add_card_mul_nashError` applies
  only once an approximately Nash root at the displayed tail is supplied.
  The reached root is instead selected because it has a fixed profitable
  endpoint.
* On an exact minimum Nash row, a positive singleton clock does force every
  positive debtor to be its owner
  (`minimumExactNash_positiveSingletonClock_positiveDebt_owner_eq`).  Again,
  the reached row has no such Nash provenance.
* Singleton-tight iteration can then yield player deletion or a stationary
  handoff, but its hypotheses require a minimum carrier face and a controlled
  exact solo root.  A positive singleton event in an arbitrary actual prefix
  supplies neither.

Therefore no prescribed-payoff exact charged path, near-return, uniform
payoff, or maintained natural-valued descent follows from the reached
singleton with the presently checked fields.  Calling its cardinality drop a
rank decrease would be circular: the next collision invocation requires the
unsigned activation of Lemma 3.1, which increases the marked support again.

## 6. Exact surviving interface

The first genuinely missing datum is not another incidence label.  It is one
of:

1. macroscopic conditional dominance (4.3) for a source-matched hard
   collider;
2. control of the off-singleton endpoint rows sufficient to sign `G_c`; or
3. an independent theorem converting an unsigned near-minimum activation
   into a floor-admissible Bellman edge.

None is a field of the current hard residual.  Accordingly this note is an
internal finite-regeneration repair and a stopping criterion, not an export
candidate.

## 7. Sources inspected

Checked declarations/files:

* `causalCollision_tailEscape_or_quantitativeNearMinimumTransfer` and
  `causalCollision_tailEscape_or_quantitativeRecipientAtom` in
  `TerminalSemanticCausalCollisionMinimumTransfer.lean` and
  `TerminalSemanticCausalCollisionRecipientAtom.lean`;
* `negativeMoat_or_positive_pairReplacement` and
  `exists_negativeMoat_or_pairReplacement_of_dropout` in
  `TerminalSemanticPlateauPairDropoutConsumer.lean`;
* `exists_terminalGap_collision_at_singleton` in
  `Collision/SingletonPacket/PunishmentNormalAtomicCollisionHandoff.lean`;
* `singletonMass_mul_otherDebt_le_tailExcess_add_card_mul_nashError` in
  `TerminalSemanticMacroscopicAtomNashProvenance.lean`;
* `minimumExactNash_positiveSingletonClock_positiveDebt_owner_eq` in
  `OneActiveAlignedRankCollapse.lean`;
* `singletonTight_atomicHandoff_or_playerDeletion` in
  `TerminalSemanticSingletonTightMinimumFaceIteration.lean`.

Concrete next test: prove or refute (4.3) from the *co-realized* hard
principal and actual recipient-atom fields, rather than from the static
singleton collision map alone.

## 8. Delta: the minimum joint-law finite atom does not supply the sign

The reviewed/exported theorem
`FIN4_MINIMUM_JOINT_LAW_HAS_FINITE_ATOM` strengthens the source side: every
hard-residual minimum joint law has a positive finite coordinate, and the
checked causalization theorem realizes it as a literal suffix atom behind
arbitrarily deep cap--Nash prefixes.  This still does not imply (4.3).

If the selected finite coordinate is a collision, the existing macroscopic
collision dispatch applies.  If it is `{o}`, the uniform strict-singleton gap
on the minimum fiber gives, for nearby actual laws,

```text
mass(Never) + sum_{S != {o}} mass(S) >= delta/(4M).    (8.1)
```

This is the checked/previously reviewed moment estimate from the positive
minimum attainment screen.  It only supplies a compensating outcome.  That
outcome can be Never or another singleton.  Neither is an overlapping pair
for `o`, and neither signs the reached Quit insertion of the hard collider.
Indeed a normalized full-support singleton packet is itself a law supported
entirely on singleton rows, so same-table packet data cannot exclude this
case at the reward-moment level.

The deep cap--Nash prefixes do not change the conclusion.  Their roots are
exact against cap/envelope tails; the causal atom is explicitly in the
suffix, not one of those roots.  In the all-Continue cap arm, the prefixes
merely delay the same suffix with survival one.  The persistent suffix gain
then remains an unrestricted behavioral gain, but it produces neither
prefix absorption nor a Bellman charge.  Reapplying the paid cap port returns
the already checked `QuantitativeDebtDescent or InertStall` alternative; in
the all-Continue branch it gives the same inert port.

Thus none of the additional same-table inputs changes the local endpoint
calculation:

* punishment normality and the full normal core give (4.1), only on the
  advertised singleton edge;
* the full-support packet controls singleton reward moments, not the
  off-singleton rows in (4.2);
* minimum-fiber isolation controls exact roots at the minimum tail, whereas
  the reached suffix row has a fixed positive Nash defect; and
* paid/reset sources are separately selected actual profiles and cannot be
  identified with this reached suffix.

Therefore the strengthened full-data attempt still reaches the exact inert
boundary.  A proof claiming a charged edge from these fields would silently
identify the causal suffix row with a cap--Nash prefix row or silently align
a separately selected paid/reset source.  Both identifications are false at
the current interface.
