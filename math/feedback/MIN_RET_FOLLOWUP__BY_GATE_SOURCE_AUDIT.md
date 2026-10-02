# Source and freshness audit of the persistent-base fixed-law rigidity followup

Audited source: [`../MIN_RET.md`](../MIN_RET.md), section `## Followup`.

Repository commit inspected: `b9429740b4db40bd4f2a6d04df7fe8b35609e267`.
The unrelated working-tree changes in the absorption-path/root-law files were
not used in this audit.

## Verdict

**FAIL for export in its present form.**

The central fixed-law rigidity theorem is mathematically correct, genuinely
new relative to the declarations and conference records found by the narrow
search, and it closes the previously explicit distinction between the
pair-base stationary target and the reset-returned semantic pair. It is worth
retaining and preparing as a standalone packet.

Two corrections are required before export:

1. the limiting erasure estimate must count the genuine `Never` outcome in
   its exceptional event; and
2. the claimed maximal-root/unique-all-Continue exit is not new and is not
   supplied by the fixed-law reset dispatch alone. The reset dispatch gives
   only an all-Continue exact-root/fixed-point arm. The stronger
   positive-child-or-unique-all-Continue alternative is already checked by
   `maximalOneStepPaidResetRegeneration_or_uniqueAllContinue` and does not need
   the new rigidity theorem.

After those corrections, the source/freshness gate passes for the rigidity
theorem and the exact identity `returned = target`. A final export should make
those, rather than the already-checked maximal-root alternative, its claimed
new content.

## Claim audited

Let `I` be finite, let `B` have at least two members, and let `sigma` be an
actual behavioral profile whose first live root makes every member of `B`
Quit surely. Let

```text
x  = terminal semantic pair of sigma,
nu = complete terminal outcome law of sigma.
```

Assume every player outside `B` has zero semantic debt at `x`. For any joint
carrier point `(y,nu)` with the same complete law, the claimed conclusion is

```text
x.cap_i <= y.cap_i   for every i.
```

It follows that `D(x) <= D(y)`, and if also `D(y) <= D(x)`, then `y=x`.

The note separately applies this to the explicit Fin4 pair-base stationary
target and the same-law point returned by the fixed-law reset minimization.

## Mathematical check

### The rigidity proof is sound

For a free player `k` outside `B`, zero debt at the actual target says
`x.cap_k=x.payoff_k`. Any joint-carrier semantic pair has nonnegative debt, so
`y.cap_k>=y.payoff_k`. Equality of the complete law already forces equality
of prescribed payoff moments, hence `y.payoff_k=x.payoff_k`. Thus
`x.cap_k<=y.cap_k`.

For `i` in `B`, choose `j` in `B\{i}`. Every outcome of the actual target law
is an absorbing coalition containing all of `B`. Define

```text
E_i(nu) = sum over nonempty coalitions S of
          nu(some S) * r_i(S \ {i}).
```

Erasure never makes the coalition empty because `j` remains. At the actual
target, every behavioral replacement of `i` is strategically reduced to its
date-zero mixture:

- Quit at date zero gives the prescribed payoff `x.payoff_i`;
- Continue at date zero leaves `j` quitting surely and gives `E_i(nu)`.

The game absorbs at that date in either case, so later behavior is irrelevant.
Consequently

```text
x.cap_i = max(x.payoff_i, E_i(nu)).
```

Now take a realizing sequence for `(y,nu)` and replace `i` by literal Never.
On every coupled original path whose terminal coalition contains `j`, the
histories and actions before absorption are unchanged and the new terminal
coalition is exactly the old coalition with `i` erased. On the complementary
event the deviating payoff is merely bounded below. The complementary event
has probability tending to zero because the limiting law is concentrated on
coalitions containing `B`. Hence the limiting cap satisfies

```text
y.cap_i >= E_i(nu).
```

Carrier debt nonnegativity also gives `y.cap_i>=y.payoff_i=x.payoff_i`, proving
the coordinatewise comparison. Equality of total debts then forces equality
of every cap coordinate.

This uses one legal behavioral deviation, Never, only as a lower bound on the
full unrestricted cap. It therefore covers the complete unilateral behavioral
class, including randomized and arbitrarily late deviations; it does not
replace that class by stationary deviations.

### Required correction to the displayed estimate

The repository's terminal outcome type is

```text
Option {S : Finset I // S.Nonempty},
```

where `none` is genuine Never/nonabsorption. Formula (8) in the note is written
only with coalitions `S`. For an approximating profile, its exceptional event
must be

```text
{none} union {some S : j notin S},
```

not just the finite coalitions omitting `j`. The limiting target gives this
whole event mass zero, so the proof is unchanged after the correction. But the
event has to be stated literally; otherwise positive Never mass in a realizing
profile is omitted from the error term.

The same-law hypothesis can also be sharpened: no separate equality of the
prescribed payoff vectors is needed. For two joint-carrier points over the
same complete law, `terminalSemanticLawCarrier_rewardMoment` supplies it.

## Exact source correspondence

The following checked declarations supply the application but do not prove
the new rigidity comparison.

### Pair-base target and solved free coordinates

`UniformEquilibrium/Diagnostics/Quitting/Collision/SingletonPacket/PairBaseStationaryDebtLocalization.lean`

```text
FinFourPairBaseStationaryDebtLocalization
nonempty_finFourPairBaseStationaryDebtLocalization
FinFourPairBaseStationaryDebtLocalization.free_solved
```

The target is a literal stationary profile based on
`quittingPersistentBaseRoot`; the prescribed two-player base Quits surely,
and `free_solved` is zero debt against unrestricted behavioral deviations.
The same structure also retains the base debtor and the paid
first-disagreement row.

`UniformEquilibrium/Diagnostics/Quitting/Collision/Toggles/PersistentBaseInducedGame.lean`
and
`UniformEquilibrium/Diagnostics/Quitting/Collision/Toggles/PersistentBaseNashSemanticAdapter.lean`
contain the induced-game semantics used by this construction, notably
`persistentBase_inducedNash_free_semantics` and the persistent-base root
identities. They do not compare caps of two different joint-carrier points
with the same law.

### Same-profile paid/reset adapter

`UniformEquilibrium/Diagnostics/Quitting/Collision/SingletonPacket/PairBasePaidResetAlignment.lean`

```text
FinFourPairBasePaidResetTarget
nonempty_finFourPairBasePaidResetTarget
QuittingTerminalExploitabilityWitness.exists_finFour_pairBasePaidResetDispatch
```

These give one actual target profile/law with a solved reset owner, unit
incidence, and the pair-localized paid row, then apply the fixed-law reset
dispatcher.

`UniformEquilibrium/Diagnostics/Quitting/Collision/SingletonPacket/PairBasePaidResetPayoffAlignment.lean`

```text
QuittingFixedLawResetDispatch.prescribed_eq_target
QuittingTerminalExploitabilityWitness.
  exists_finFour_pairBasePaidResetDispatch_payoffAligned
```

These prove equality only of the prescribed payoff vectors, because the
complete law fixes its reward moment. They explicitly do not identify the cap
coordinates.

`UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/Endpoint/FinFourSameSourcePaidResetCapPort.lean`

```text
FinFourPairBasePaidResetTarget.capLiftedSource
FinFourSameSourcePaidResetCapPort
QuittingTerminalExploitabilityWitness.
  nonempty_finFourSameSourcePaidResetCapPort
```

This already packages the same actual stationary target as the paid/reset
source and its cap-lifted port. It deliberately retains the reset-returned
pair as a separate object. Thus it confirms that the new equality closes a
real, previously exposed seam rather than duplicating this wrapper.

### Fixed-law comparison fields

`UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticResetIncidenceCapReturn.lean`

```text
QuittingFixedLawResetDispatch.joint
QuittingFixedLawResetDispatch.target_ge
QuittingFixedLawResetDispatch.dynamic_exit
```

For the pair-base application, `joint` puts `(returned,target.mass)` in the
joint carrier and `target_ge` states

```text
D(returned) <= D(target).
```

The new rigidity theorem supplies the reverse inequality coordinatewise and
hence proves `returned=target`. This cap comparison was not found among the
existing declarations.

`UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticResetIncidenceReturn.lean`

```text
terminalSemanticLawCarrier_rewardMoment
mem_terminalSemanticLawCarrier_of_joint_tendsto
```

The first removes the redundant prescribed-payoff hypothesis. The carrier is
defined as the closure of actual joint semantic/law points, so the ordinary
mathematics proof may use a realizing sequence; the second is the forward
sequence-to-carrier direction, while the reverse extraction follows from the
same `mem_closure_iff_seq_limit` representation used in this module.

### Existing maximal-root alternative

`Research/Quitting/PaidCapMaximalOneStepRegeneration.lean`

```text
QuittingPaidCapLiftedSource.HasUniqueAllContinueAtCap
QuittingPaidCapLiftedSource.MaximalOneStepPaidResetRegeneration
QuittingPaidCapLiftedSource.
  maximalOneStepPaidResetRegeneration_or_uniqueAllContinue
```

This already proves, from an actual paid/reset source, the exhaustive
alternative

```text
positive-absorption maximal root with an actual strict-debt descendant
or every exact root at that cap is all-Continue.
```

The pair-base target already becomes such an actual source through
`FinFourPairBasePaidResetTarget.capLiftedSource`. This theorem does not depend
on identifying the fixed-law returned point with the target.

By contrast, `QuittingFixedLawResetDispatch.dynamic_exit` alone gives, after
the new equality is substituted,

```text
positive-absorption exact root with a strict target child
or all-Continue is one exact root and fixes the target.
```

It does not say that all-Continue is maximal or unique. Therefore Section 3
of the followup must cite the maximal-root theorem as an already-checked,
independent corollary and must not present that alternative as new content of
the rigidity argument.

## Freshness conclusion

The narrow search found no Lean declaration or conference theorem proving
either of the following:

1. coordinatewise cap minimality of a sure-quitting persistent-base profile
   among all joint-carrier points with its complete terminal law; or
2. equality of the Fin4 pair-base stationary target with its fixed-law
   reset-returned semantic pair.

Earlier pair-base audits explicitly retained `returned.1=target.1` while
warning that `returned.2=target.2` was not known. The followup's erasure
argument closes exactly that gap.

The positive-child/unique-all-Continue alternative is not fresh: it is the
checked maximal-root theorem above.

## Export repairs and boundary tests

A standalone export should:

1. state the law on `Option` outcomes and include `none` in the erasure error;
2. derive prescribed-payoff equality from the common law rather than assume
   it;
3. claim as new only the coordinatewise cap comparison and
   `returned=target` application;
4. describe the maximal-root alternative as an existing downstream theorem,
   not as a new consequence unique to this proof;
5. include an explicit negative boundary test for a singleton base: when
   `|B|=1`, continuing can expose the later tail and erasure can produce the
   empty/Never outcome, so the two-endpoint formula need not hold;
6. record that zero debt of the nonbase players is essential to their cap
   comparison; and
7. give Lean-facing theorem shapes such as
   `persistentBase_fixedLaw_cap_le` and
   `FinFourPairBasePaidResetTarget.returned_eq_target`, without storing the
   desired comparison as an input field.

With those repairs, the theorem is a legitimate exact source-alignment
result. It does not consume the unique-all-Continue stall, make strict debt
descent well founded, or prove a uniform-equilibrium payoff.
