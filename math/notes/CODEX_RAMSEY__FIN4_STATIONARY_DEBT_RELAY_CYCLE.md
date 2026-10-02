# Fin4 stationary debt-relay cycle from prescribed-owner handoffs

Author: `CODEX_RAMSEY`

Status: **core ordinary-mathematics theorem independently PASSed** by
[`CODEX_EULER`](../feedback/CODEX_RAMSEY__FIN4_STATIONARY_DEBT_RELAY_CYCLE__BY_CODEX_EULER.md).
The later bounded connector test is an internal field-level failed
implication; it is not an exported theorem or a conjecture counterexample.

This note consumes the reviewed prescribed-owner alignment in
[`FIN4_PRESCRIBED_OWNER_LABEL_HANDOFF_ALIGNMENT`](../formalized/FIN4_PRESCRIBED_OWNER_LABEL_HANDOFF_ALIGNMENT.md).
It does not edit or strengthen that packet.  The whole-packet review used here
is
[`FIN4_PRESCRIBED_LABEL_HANDOFF_ALIGNMENT__BY_CODEX_RAMSEY__PACKET_GATE`](../feedback/FIN4_PRESCRIBED_LABEL_HANDOFF_ALIGNMENT__BY_CODEX_RAMSEY__PACKET_GATE.md).

## Question

The prescribed-owner theorem gives an actual singleton-base source and an
actual unilateral owner repair for every preselected label, but returns the
new paid debtor.  Does finiteness force more than four unrelated label
statements?

The answer below is a small positive one.  After one simultaneous finite
selection, the returned debtor labels contain a directed cycle.  Every arrow
of that cycle is co-realized on one actual source/repair pair: the tail is the
unique debtor of the source, its Always-Continue repair gains uniformly and
kills that debt, and the head is a distinct full-gap debtor with a literal
paid row on the repaired profile.

This is not a chronological cycle of profiles.  The exact remaining seam is
the missing identification or connector between one repaired profile and the
next independently reselected singleton-base source.

## Exact statement

Let the player type be literally `Fin 4`, let

```text
reward : {S : Finset (Fin 4) // S.Nonempty} -> Payoff (Fin 4),
witness : QuittingTerminalExploitabilityWitness reward,
Gamma = witness.terminalGap > 0.
```

For a stationary root `q`, write `sigma(q)` for its stationary behavioral
profile and

```text
d_i(sigma(q))
  = quittingStationaryUnilateralCap reward q i
      - quittingTerminalPayoff reward (sigma(q)) i.
```

This equals the actual unrestricted terminal-semantic debt of the literal
stationary profile by
`quittingTerminalSemanticPair_stationary_envelope_eq_cap`.

### Theorem: finite co-realized debt-relay cycle

There exist

```text
delta > 0,
m in {2,3,4},
pairwise distinct labels a_0,...,a_(m-1),
```

and, for every cyclic index `t mod m`, an induced Nash point `z_t`, a source
profile `sigma_t`, and its repaired profile `tau_t` such that the following
hold.  Put `a_m=a_0`.

1. **Literal source and unilateral repair.**

   ```text
   z_t in quittingPersistentBaseNashSet
     reward {a_t} (univ.erase a_t),

   sigma_t = quittingSingletonBaseStationaryProfile
     reward a_t (univ.erase a_t) z_t,

   tau_t = update sigma_t a_t
     (quittingAlwaysContinueStrategy reward a_t).
   ```

   Thus this is one actual behavioral-strategy replacement, not a comparison
   between two semantic carrier limits.

2. **Unique-debtor source and uniform gain.**

   ```text
   d_(a_t)(sigma_t) >= delta,
   d_j(sigma_t)=0                         for every j!=a_t,

   U_(a_t)(tau_t)-U_(a_t)(sigma_t) >= delta,
   d_(a_t)(tau_t)=0.
   ```

   Every free coordinate of `sigma_t` attains its unrestricted behavioral
   cap and lies above its punishment value.  The repaired owner payoff also
   lies above its punishment value.

3. **The next cyclic label is the co-realized paid debtor.**

   ```text
   a_(t+1) != a_t,
   d_(a_(t+1))(tau_t) >= Gamma,
   Nonempty (QuittingPaidFirstDisagreementRow
     reward tau_t a_(t+1) Gamma).
   ```

   Thus the cycle arrow `a_t -> a_(t+1)` records a positive debt transfer on
   the same actual repaired profile that carries the paid row.  It is not
   inferred merely from a reward-table sign.

4. **Floor alternative.**  At every phase either all coordinates of `tau_t`
   lie above punishment, or a displayed free coordinate lies strictly below
   punishment.  Consequently either one phase exposes such a localized floor
   failure, or all repaired profiles in the relay cycle are floor safe.

## Proof

### 1. Select one actual handoff for each prescribed owner

For every `d : Fin 4`, apply

```text
QuittingTerminalExploitabilityWitness.exists_prescribedOwner_stationaryHandoff
```

from
`UniformEquilibrium/Diagnostics/Quitting/Collision/Toggles/PrescribedOwnerStationaryHandoff.lean`.
It returns a number `delta_d>0`, uniformly valid over the singleton-base
induced Nash carrier, and also returns one actual point of that carrier with a
nonempty

```text
QuittingSingletonBaseStationaryHandoff
  reward d (univ.erase d) z_d delta_d Gamma.
```

Choose one such handoff `H_d` for every `d`.  Define

```text
f(d) = H_d.outsideDebtor.
```

The checked field `outsideDebtor_ne_owner` gives `f(d)!=d`.

The fields `source_free_semantics` and `source_owner_debt`, together with
`quittingTerminalSemanticPair_stationary_envelope_eq_cap`, say that the source
has debt zero in every coordinate other than `d` and debt at least `delta_d`
in coordinate `d`.  The identity

```text
update_quittingSingletonBaseStationaryProfile_owner_alwaysContinue
```

identifies the repaired profile with the literal unilateral update.  The
fields `repaired_owner_gain`, `repaired_owner_cap_eq_payoff`, `outside_debt`,
and `paid_row` give the remaining same-profile conclusions with
`f(d)` as debtor.

### 2. Uniformize the owner gain

There are only four positive numbers `delta_d`.  Set

```text
delta = min {delta_d : d in Fin 4}.
```

The set is finite and nonempty, and every member is positive, so `delta>0`.
Every selected owner debt and repair gain is at least `delta`.

### 3. Extract a simple cycle

Iterate the self-map `f` from any label.  Among its first five values two are
equal.  Remove the transient prefix and choose the first repeated block.  It
is a simple directed cycle of `f`; its length is at most four.  Since
`f(d)!=d` for every `d`, its length is at least two.  Denote its successive
labels by `a_0,...,a_(m-1)`.  Restricting the already selected handoffs
`H_d` to these labels proves all assertions in the theorem.

The floor alternative is the finite disjunction of the checked
`floor_dispatch` field.  No compactness, limiting profile, public
randomization, or restricted deviation class is introduced.

## What is new, and what is not

The individual phase data are the checked fields of
`QuittingSingletonBaseStationaryHandoff`; the reviewed prescribed-owner
wrapper makes them available for every preselected owner.  The new ordinary
mathematics is only the simultaneous finite selection, uniform positive gain,
and functional-graph extraction showing that the paid debtor can always be
chosen as the next repaired owner in a simple cycle of length two, three, or
four.

This is stronger than a label-only cycle: every arrow has one co-realized
source, unilateral deviation, debt removal, new full-gap debt, and paid row.
It is weaker than the needed paid-return producer because different arrows
use independently selected induced Nash points.

A narrow search of the collision/toggle subtree found no declaration
packaging this finite relay cycle.  The newer checked
`FinFourChargedGateSourceMatchedOwnerHandoffs` in
`UniformEquilibrium/Diagnostics/Quitting/Collision/Toggles/ChargedSoloBlockerClosureDispatch.lean`
aligns two handoff families at one owner label, but explicitly keeps their
reset target, stationary point, law, and chronology separate.  It neither
contains nor supplies the cycle above.

No external paper result is used.

## Operational essential-support passport does not close the seam

The independently audited
[`OPERATIONAL_ESSENTIAL_SUPPORT_REDUCTION`](CODEX_CEDAR__OPERATIONAL_ESSENTIAL_SUPPORT_REDUCTION.md)
starts from a terminal approximate equilibrium of a proper survivor game,
lifts it by making every deleted player play literal Never, and localizes an
ambient finite quit-time gain to one deleted player.  This is a useful local
passport, but its quiet-lift source is reselected with the survivor profile.

It cannot be applied at `sigma_t`, where `a_t` Quits surely rather than Never.
At `tau_t`, the old owner does play Never, but the co-realized next debtor has
unrestricted debt at least `Gamma`; after deleting only the old owner, the
survivor profile is therefore not an `epsilon`-Nash profile for
`epsilon<Gamma`.  More general deletion blocks again reselect their survivor
profiles.  The passport supplies no equality with `tau_t`, preserves neither
the handoff's terminal law nor its paid row, and does not make its output equal
to `sigma_(t+1)`.

Thus applying the operational reduction would lose the co-realization just
proved.  Notice also that `tau_t` already carries the stronger source-matched
finite pure-time paid row for `a_(t+1)`; the missing datum is a connector, not
another deviation witness.  Any stronger support passport which additionally
names a positive-reach root or a solo/joining coalition would still need an
explicit equality or successor relation with this actual `tau_t` before it
could change that conclusion.

## Bounded connector test: exact obstruction

Fix one relay arrow and abbreviate

```text
d = a_t,                    j = a_(t+1),
q = quittingSingletonBaseRepairedRoot d (univ.erase d) z_t,
tau_t = quittingStationaryProfile reward q.
```

The most direct retraction attempt forces the new debtor to Quit surely:

```text
q^[j] = update q j (PMF.pure true).
```

As a product row, `q^[j]` can be written with persistent base `{j}` and free
set `univ.erase j`.  To enter the next checked handoff without re-solving, its
three remaining marginals would have to define a point of

```text
quittingPersistentBaseNashSet reward {j} (univ.erase j).       (C1)
```

### Failed implication C1

The fields of `QuittingSingletonBaseStationaryHandoff` do **not** imply (C1).
They say:

- all players other than `d` are unrestricted-cap optimal at the source row
  where `d` Quits surely;
- `d` is cap optimal after its Always-Continue repair;
- `j` has positive debt and a paid pure-time pair at the repaired row.

No field gives the best-response signs of either remaining label `k,l` after
`j`, rather than `d`, is made the sure quitter.  Those are different entries
of the reward table.

This logical independence can be seen coordinatewise.  Keep the `d`- and
`j`-coordinate reward tables fixed, and keep every `k`-coordinate reward on a
coalition containing `d` fixed.  Then all source optimality fields, the owner
repair, and the new debtor/paid-row fields used above are unchanged.  Varying
instead the `k`-coordinate reward on coalitions containing `{j,k}` but not
`d` shifts `k`'s Quit advantage under the forced base `{j}`.  A sufficiently
positive or negative shift violates whichever pure/mixed best-response
condition the unchanged `k` marginal would need in (C1).  The handoff record
contains no repaired-`k` cap equality that could prevent this shift.  Its
floor field is deliberately only the inclusive safe-or-explicit-violation
disjunction.

This is an interface-level failed implication, not a constructed new
counterexample to the uniform-equilibrium conjecture: an arbitrary reward
perturbation need not preserve the global terminal witness.  It proves that
the checked handoff fields alone cannot justify the retraction.  A successful
same-table theorem must use additional global counterexample structure and
produce new cross-coordinate inequalities.

### No strict rank consequence from failure

The natural debt-support rank runs in the wrong direction.  At the source,

```text
positiveDebtSupport(sigma_t) = {d}.
```

At the repaired target, the checked fields give

```text
d_d(tau_t)=0,        d_j(tau_t)>=Gamma>0,        j!=d.
```

Hence the old debtor leaves and a new debtor enters, but

```text
1 <= card positiveDebtSupport(tau_t) <= 3
  =? card positiveDebtSupport(sigma_t)=1.
```

In particular cardinality cannot strictly decrease on this arrow.  The other
two repaired debts are uncontrolled, so it may stay one or increase.  Total
debt is also unoriented: the source lower bound `delta` and target lower bound
`Gamma` have no comparison, and no conservation identity for the remaining
coordinates is stored.

The floor data give only the exact alternative already recorded: all of
`tau_t` is floor safe, or some free coordinate is below floor.  At the source
only the free coordinates are known floor safe; its owner payoff may be below
floor even though its cap is above.  Thus the number or set of floor
violations is not monotone either.

### Connector-test verdict

Neither tested direction follows from the approved alignment:

1. forcing the next debtor to become the singleton base does not force
   induced-Nash membership; and
2. failure of that membership yields a residual best-response sign, but no
   strict total-debt, debt-support-cardinality, or floor-violation rank
   decrease.

The exact remaining positive input would have to be one of:

- a same-table theorem coupling the two untouched players' forced-`j`
  best-response signs to the paid row at `tau_t`; or
- a different well-founded obstruction sensitive to **which** debtor label
  is replaced, not merely the cardinality or total size of debt support.

No checked declaration with either conclusion was found in the inspected
persistent-base and singleton-packet neighborhood.

## Sharp nonclaims and failed implication

The tempting concatenation

```text
sigma_t --owner repair--> tau_t = sigma_(t+1)
```

is not proved and is generally unsupported by the fields.  The profile
`sigma_(t+1)` makes `a_(t+1)` Quit surely and is selected from a different
singleton-base induced Nash game.  At `tau_t`, the same label is merely a
returned debtor and may mix or Continue.  Neither payoff equality nor
terminal-law equality follows.

Accordingly the theorem does **not** give

- a behavioral or Bellman path around the cycle;
- a punishment-floor-admissible charged edge;
- monotonicity of total debt (other repaired coordinates may acquire debt);
- a state-space rank decrease;
- a payoff near-return, positive admissible closure, or uniform-equilibrium
  payoff.

The smallest remaining question is exact: can one choose the handoff for
`a_(t+1)` so that its singleton-base source is an admissible successor of
`tau_t`, or can failure of that choice be converted into a strict
carrier-debt/support decrease?  The reviewed owner alignment alone supplies
neither implication.

## Sources inspected

- `formalized/FIN4_PRESCRIBED_OWNER_LABEL_HANDOFF_ALIGNMENT.md` and its
  packet-gate feedback linked at the top;
- `QuittingTerminalExploitabilityWitness.exists_prescribedOwner_stationaryHandoff`
  in
  `UniformEquilibrium/Diagnostics/Quitting/Collision/Toggles/PrescribedOwnerStationaryHandoff.lean`;
- `QuittingSingletonBaseStationaryHandoff`,
  `exists_singletonBaseStationaryHandoff`, and
  `update_quittingSingletonBaseStationaryProfile_owner_alwaysContinue` in
  `UniformEquilibrium/Diagnostics/Quitting/Collision/Toggles/LargeBaseStationarySemanticHandoff.lean`;
- `quittingTerminalSemanticPair_stationary_envelope_eq_cap` in
  `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticNegativeVertexGerm.lean`;
- `FinFourChargedGateSourceMatchedOwnerHandoffs` and
  `FinFourChargedSoloBlockerGateLimit.nonempty_sourceMatchedOwnerHandoffs_of_debtSum_le`
  in
  `UniformEquilibrium/Diagnostics/Quitting/Collision/Toggles/ChargedSoloBlockerClosureDispatch.lean`.

## Requested check

Independently falsify the simultaneous-choice and finite-cycle step, the
translation from stationary caps to unrestricted terminal-semantic debt, the
uniform `delta`, the exact same-profile repair/paid-row provenance, and the
nonchronological boundary.  In particular, reject the theorem if any checked
field fails to survive the selection of `f(d)=H_d.outsideDebtor`.
