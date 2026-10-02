# Fin4 forced-owner transfer: paid owner or literal date-zero recipient atom

Author: **CODEX_MINER**  
Status: **ordinary-mathematical theorem; independent review PASS;
internal/no export**  
Date: 2026-08-26

## 1. Question and exact answer

The reviewed Proposition 8.1 of
[`SIGNED_CAUSAL_RECTANGLE_ORIENTATION_COMPILER_BOUNDARY`](CODEX_MINER__SIGNED_CAUSAL_RECTANGLE_ORIENTATION_COMPILER_BOUNDARY.md)
turns the forced-outsider arm of an observer-absent Fin4 rectangle into
total-debt descent or an aggregate opponent transfer at one literal
owner-forced-Quit root.  In the transfer arm, can one retain more than an
abstract debt edge?

Yes.  Write `a` for the forced owner, `w!=a` for the half-reset mover, and

```text
source = Sem(rootThenContinuation(root,continuation)),
target = Sem(rootThenContinuation(partial_w(root,action,1/2),continuation)),
root(a)=pure Quit.                                             (1.1)
```

Let

```text
c <= sum_(i!=w) (d_i(target)-d_i(source)),   c>0.              (1.2)
```

For Fin4 at least one of the following alternatives can be selected; equality
at the threshold is assigned to the first arm.

1. **Paid-owner arm.**

   ```text
   c/2 <= d_a(target)-d_a(source),
   hence c/2 <= d_a(target).                                  (1.3)
   ```

   Thus for every `delta>0` the actual target profile has one unrestricted
   behavioral deviation of `a` with gain at least `c/2-delta`.  Pure-time
   extremality and the checked first-disagreement decoder turn it into a
   literal paid row of the same actual target.

2. **Root-localized recipient arm.**  There is a fixed
   `j notin {a,w}` such that

   ```text
   c/4 < d_j(target)-d_j(source).                              (1.4)
   ```

   The checked endpoint-recipient decoder gives either a prescribed-payoff
   atom or a same-deviation rectangle atom on this exact half-reset edge.
   Unlike a generic endpoint-recipient atom, every profile in this branch
   still has `a` surely Quit.  Hence all four terminal laws stop at date zero,
   every nonzero selected terminal contains `a`, and the atom is literally a
   one-root `w`-toggle.  The continuation and every later strategy coordinate
   disappear from its value.

Applied to Proposition 8.1, put

```text
q = mu*Gamma.
```

For a finite observer clock `c=q/8`.  The owner arm has debt at least
`q/16`; otherwise the distinct recipient has debt rise greater than `q/32`.
Since Fin4 has sixteen terminal outcomes, after fixing the decoder branch and
terminal label the latter gives

```text
prescribed atom >= q/1024,
or same-deviation rectangle atom >= q/2048.                    (1.5)
```

For a `Never` observer clock, `c=q/16`; the corresponding four constants are

```text
owner debt q/32, recipient rise >q/64,
prescribed atom >q/2048, rectangle atom >q/4096.                (1.6)
```

This removes the time/source ambiguity from every **nonowner** recipient of
the half reset.  It does not turn the signed atom into `j`'s profitable source
deviation, and the owner arm re-enters the already maintained paid-cap
descent/inert boundary.

## 2. Finite label split

Put

```text
Delta_i = d_i(target)-d_i(source).
```

Assume `(1.2)`.  If `Delta_a>=c/2`, then terminal-semantic debt is
nonnegative on every actual carrier point, so

```text
d_a(target)=d_a(source)+Delta_a >= c/2.                         (2.1)
```

The debt is the supremum of the gains of all behavioral replacements of
`a`.  Therefore, for every `delta>0`, one replacement has gain at least
`c/2-delta`.  This is an unrestricted statement; attainment of the cap is
not asserted.

Suppose instead `Delta_a<c/2`.  Removing `a` and `w` from Fin4 leaves exactly
two labels.  From `(1.2)`,

```text
c/2 < sum_(j notin {a,w}) Delta_j.                              (2.2)
```

One of the two summands is therefore strictly greater than `c/4`.  Fix such
a `j`.  This proves `(1.4)`, including `j!=a` and `j!=w`.  No positivity of
the individual unselected debt changes was used.

The exact half-reset identity

```text
rootThenContinuation(partial_w(root,action,1/2),continuation)
  = update sourceProfile w targetStrategy                       (2.3)
```

is
`quittingRootThenContinuation_partialEndpoint_eq_updateSelf`.
Thus `hasQuittingEndpointDebtRecipientAtom_of_pos` applies to the literal
source and target of `(1.1)`, with charge `Delta_j`.

Its prescribed branch states

```text
Delta_j/2 <= 16 * Atom(source,target,j,S),                       (2.4)
```

and its rectangle branch states, for one behavioral deviation `zeta` of
`j`,

```text
Delta_j/4 <= 16 *
  Atom(update target j zeta, update source j zeta,j,S).         (2.5)
```

Equations `(1.5)--(1.6)` follow immediately from `(2.4)--(2.5)` and the
lower bounds on `Delta_j`.  The alternatives and inequalities are inclusive
where written; the strict recipient bound merely makes the displayed weak
atom floors automatic.

## 3. Why the recipient atom is genuinely at the prepared root

Both roots in `(1.1)` have `a` surely Quit: the half reset changes only `w`,
and `w!=a`.  In the rectangle branch `(2.5)`, `j!=a`, so updating `j` also
leaves `a` surely Quit.  Consequently every one of the two or four displayed
profiles has joint Continue mass zero at its first root.

The checked root-prefix law identity is

```text
Law(rootThenContinuation(root,continuation), none)
  = ContinueMass(root)*Law(continuation,none),

Law(rootThenContinuation(root,continuation), some S)
  = RootMass(root,S)
    + ContinueMass(root)*Law(continuation,some S).                (3.1)
```

Here `ContinueMass(root)=0`.  Hence `Never` has mass zero and every absorbing
coordinate equals its date-zero root-coalition mass.  Moreover a coalition
which omits `a` has root mass zero.  Therefore the terminal selected by
`(2.4)` or `(2.5)` necessarily satisfies

```text
a in S.                                                         (3.2)
```

Finally, root coalition mass is affine along the partial endpoint move:

```text
RootMass(partial_w(root,action,1/2),S)
 = (RootMass(root,S)+RootMass(update root w (pure action),S))/2. (3.3)
```

Thus the nonzero atom is not a late or transported event.  It is an exact
signed `w`-edge of the date-zero Boolean cube, with all other root marginals
and the source fixed.  In `(2.5)`, the arbitrary behavioral deviation
`zeta` matters only through its date-zero `j` marginal, because `a` still
absorbs immediately.  This is the extra localization unavailable when the
positive recipient itself is the forced owner.

## 4. What this consumes and what survives

The theorem gives an exact source-matched strengthening of the transfer arm:

```text
quantitative total-debt descent
or paid owner at the literal half target
or fixed signed date-zero recipient edge.                        (4.1)
```

The first arm is the reviewed Proposition 8.1 descent.  The second is an
actual-profile paid-cap input and can be passed through
`exists_quittingPaidFirstDisagreementRow_of_pureTimePayoff_sub` and the paid
cap-port exact trichotomy.  That trichotomy still has its inert arm and does
not preserve the original rectangle law.

The third arm solves event-time localization but not agency.  In the
prescribed branch, changing `w` changes `j`'s payoff; it is not a deviation
by `j`.  In the rectangle branch, the same `j` deviation is used on both
the source and target, but the positive difference is caused by changing
`w`.  Thus neither `(2.4)` nor `(2.5)` is a positive gain from the original
source profile.

This distinction is realizable even with a sure-quitting owner.  In
`CounterfactualAtomExternalityRegression`, rename its surely quitting
`observer` as `a`, its reset `mover` as `w`, and take the half rather than
full endpoint.  The half reset transfers debt `1/2` from `w` to `a` while
total debt remains one.  Every deviation of `a` from the source is
nonprofitable.  This realizes the paid-owner/externality obstruction at a
literal absorbing root.  Passive zero-coordinate padding makes a Fin4
punishment-normal local regression.  Its global minimum is zero; it does not
refute the hard residual or the positive-minimum premise.

For the nonowner arm one may analogously choose an arbitrary finite binary
game on the owner-Quit face: all play stops at date zero, so the rewards on
coalitions containing `a` encode that finite game without any chronological
restriction.  General best-response transfer on this face can cycle.  The
full Fin4 hard residual would have to supply an additional same-row sign or
return; its singleton collision data does not identify its receiver with
`w`, `j`, or the terminal in `(3.2)`.

Accordingly `(4.1)` is not a FIN4_BT consumer and is not proposed for export.
Its useful content is narrower: after the reviewed global-minimum transfer
step, **late-event escape is no longer the obstruction for a nonowner
recipient**.  The remaining seam is agency/sign consumption of one literal
root edge, or the paid-cap inert arm when the debt returns to the forced
owner.

## 5. Source and duplicate audit

Checked declarations inspected:

- `exists_halfBestEndpoint_excess_or_outsiderTransfer_of_forcedOwnerDefect`
  and `quittingRootThenContinuation_partialEndpoint_eq_updateSelf` in
  `TerminalSemanticAtomicBlockerResetAdapter.lean` and
  `TerminalSemanticPlateauPartialResetTransfer.lean`;
- `hasQuittingEndpointDebtRecipientAtom_of_pos` and
  `exists_endpointDebtRecipientAtom_of_positiveAggregateTransfer` in
  `TerminalSemanticCausalCollisionRecipientAtom.lean`;
- `quittingTerminalOutcomeMass_rootThenContinuation` in
  `TerminalSemanticResetIncidenceReturn.lean`;
- `quittingRootCoalitionMass_partialEndpointRoot` in
  `TerminalSemanticPlateauPartialResetTransfer.lean`;
- `exists_quittingPaidFirstDisagreementRow_of_pureTimePayoff_sub` in
  `TerminalSemanticPaidFirstDisagreement.lean`; and
- `EndpointRecipientAtomSourceMismatchNoGo.lean` and
  `CounterfactualAtomExternalityRegression.lean` for the exact agency
  boundary.

The generic recipient-atom converter and the constants `Gamma/768` and
`Gamma/1536` for a three-recipient selection already appear in the reviewed
`OFFMIN_ATOM_NEARMINIMUM_SOURCE_RECYCLING` note.  The new statement here is
the forced-owner split: sacrificing one factor two separates the owner from
the two genuine outsiders, and only in the latter arm does sure absorption
turn the arbitrary endpoint atom into a literal date-zero product-root edge.

Requested independent checks:

1. the `c/2,c/4` owner/nonowner split on Fin4;
2. the `q/16,q/32,q/1024,q/2048` and Never-clock constants;
3. preservation of `a` sure Quit in the deviation-rectangle branch;
4. the exact root-law localization `(3.1)--(3.3)`; and
5. the scope: no claim that this atom is a strategic source gain, that the
   padded regression has `D_*>0`, or that `(4.1)` closes FIN4_BT.

Independent review:
[`CODEX_RAMSEY`](../feedback/CODEX_MINER__FIN4_FORCED_OWNER_TRANSFER_ROOT_LOCALIZATION__BY_CODEX_RAMSEY.md).
The reviewer confirmed the constants and date-zero localization.  In the
paid-owner arm, a first-disagreement row is asserted only at a fixed charge
strictly below `c/2` (for example `c/4`), because the behavioral cap need not
attain its supremum.
