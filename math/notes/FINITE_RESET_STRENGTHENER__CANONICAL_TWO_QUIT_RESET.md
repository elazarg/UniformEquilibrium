# Canonical two-Quit reset under a terminal gap

Identity: `FINITE_RESET_STRENGTHENER`

## Status

Ordinary mathematics, independently reconstructed.  The core ingredients are
already checked Lean declarations, but the final reset-target wrapper stated
here is not checked in Lean.  This note branches from
[`FIN4_THREE_ROLE_ASCENT_FINITE_RESET_COMPILER`](../../ASCENT_NORM/FIN4_THREE_ROLE_ASCENT_FINITE_RESET_COMPILER.md).

The theorem is a strengthening of the reset-arrival output, not a solution of
the fixed-law reset dispatch's remaining dynamic alternative.

## Self-contained question

Let `I` be a finite player type and let `reward` be a finite quitting-game
reward table.  Suppose there are `gamma > 0` and a terminal exploitability gap
of size `gamma` against every behavioral profile.  Must there be one literal
profile having an exact zero-debt player and positive opponent incidence?  Can
the law and incidence be made canonical?

## Theorem: canonical simultaneous-pair reset

There are distinct players `a,b : I` such that, for the pure stationary
profile `pi` in which exactly `a` and `b` Quit surely at date zero,

```text
d_b(pi) = 0,
Inc_b(a, law(pi)) = 1.
```

Moreover, the two table inequalities

```text
gamma <= reward({a},a),
reward({a},b) + gamma <= reward({a,b},b)
```

hold.  Thus the update from the singleton profile in which only `a` Quits to
`pi`, obtained by making `b` Quit at zero, is a literal unilateral pure-time
update with gain at least `gamma`.

Only the terminal-gap tests at the all-Never profile and at the selected
singleton profile are used.  Equivalently, the theorem needs only a positive
solo owner and a distinct profitable immediate collider, as packaged by
`QuittingImmediateSingletonCollision`.

### Proof

At the all-Never profile, every unilateral behavioral deviation is capped by
the better of Never and immediate solo exit.  The gap therefore selects `a`
with

```text
gamma <= reward({a},a).
```

At the pure singleton profile `{a}`, player `a` has exact debt zero: staying
in gives `reward({a},a) >= gamma > 0`, while leaving gives the nonabsorption
payoff zero.  Applying the gap at this profile therefore selects another
player `b != a`.  Against the sure exit of `a`, every behavioral deviation by
`b` is capped by the better of staying out and joining at date zero.  Because
the prescribed strategy stays out, the positive gap forces

```text
reward({a},b) + gamma <= reward({a,b},b).
```

Now update `b` to Quit at date zero.  Against the unchanged opponents, the
displayed inequality says this update attains `b`'s complete behavioral cap.
Hence `d_b(pi)=0`.  The terminal law is the point mass at `{a,b}`, so every
terminal coalition contains `a` and `Inc_b(a,law(pi))=1`.

This proof controls unrestricted behavioral deviations, not merely
stationary deviations: `quittingTerminalPayoff_update_pureSetRoot_le` gives
the all-behavior membership-toggle cap.

## Relation to an arbitrary start profile

For any behavioral start profile, the canonical `pi` can be reached by at
most `card I` unilateral pure-time coordinate updates: update `a` and `b` to
Quit at zero and every other coordinate to Never, in any enumeration.  These
coordinate rewrites are literal, but they need not be profitable.  Therefore
this observation is provenance only; it is not a backward equilibrium
compiler.

If every edge is required to be profitable, use the strengthened acquisition
argument in the accompanying independent review.  It gives at most
`card I + 3` profitable pure-time updates from an arbitrary profile, though
its final law need not be the canonical pair law.  The acquisition subchain
and its `card I + 1` bound are already checked as
`exists_bounded_quittingPureTimeSelfResetChain`; only the final exact
zero-debt/incidence finish is new mathematics here.

## Existing declarations supplying the proof

- `QuittingTerminalExploitabilityWitness.exists_terminalGap_le_soloReward`
  and `QuittingTerminalExploitabilityWitness.exists_collision_gain` in
  `UniformEquilibrium/Quitting/Classification/TerminalExploitabilityToggles.lean`;
- `QuittingTerminalExploitabilityWitness.exists_immediateSingletonCollision`
  in
  `UniformEquilibrium/Diagnostics/Quitting/Collision/ImmediateSingletonCollision.lean`;
- `QuittingImmediateSingletonCollision.margin_le_collider_gain` and
  `QuittingImmediateSingletonCollision.collider_debt_eq_collisionGain` in
  `UniformEquilibrium/Quitting/Classification/ImmediateSingletonCollision.lean`;
- `quittingTerminalSemanticDebt_pureSetRoot_eq` and
  `quittingTerminalPayoff_update_pureSetRoot_le` in
  `UniformEquilibrium/Quitting/Paths/SureExitSet.lean`.
- `exists_bounded_quittingPureTimeSelfResetChain` in
  `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticBoundedSelfReset.lean`,
  for the separate all-profitable arbitrary-start acquisition path.

The last zero-debt-at-the-updated-pair and unit-incidence wrapper does not
appear in the narrow symbol search.  Existing Fin4 reset producers instead
use induced stationary Nash faces, for example
`QuittingTerminalExploitabilityWitness.exists_finFour_prescribedOwner_resetDispatch`
in
`UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticFinFourPrescribedOwnerResetAlignment.lean`.

## Boundary tests

1. A terminal gap forces at least two players.  This is already checked as
   `QuittingTerminalExploitabilityWitness.one_lt_card`.
2. Positivity of the first solo payoff is essential for ruling out the owner
   as the singleton profile's exploiter.  The terminal gap supplies the
   stronger lower bound `gamma`.
3. The final reset owner is the collider `b`, not the solo owner `a`.
4. Unit incidence follows from the literal pair law and is stronger than mere
   positive incidence.

## Scope and next question

The theorem gives an arbitrary-finite-player actual reset target and can feed
`exists_fixedLawResetDispatch` from any supplied positive global-minimum
source.  It does not retain an incoming endpoint law, mover, recipient, or
routed atom.  It also does not consume the reset dispatch's all-Continue arm.

Concrete next question: formalize the small wrapper from an
`ImmediateSingletonCollision` to the simultaneous-pair zero-debt/unit-incidence
target, then compare whether the endpoint-attached all-profitable path carries
any downstream datum not already present in this canonical reset.
