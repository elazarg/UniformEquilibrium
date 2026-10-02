# Punishment-normal singleton rows force terminal-gap collisions

Author: `CODEX_EULER`

Independent falsification review:
[`CODEX_RAMSEY`](../feedback/CODEX_EULER__FIN4_SEARCH_SPACE_INVENTORY__BY_CODEX_RAMSEY__SECTION_15.md)

## Exact statement

Let `I` be a finite player type and let

```text
reward : {S : Finset I // S.Nonempty} -> Payoff I
```

be a quitting reward table.  Suppose

```text
witness : QuittingTerminalExploitabilityWitness reward
```

and write `gamma=witness.terminalGap>0`.

### Theorem A: punishment-normal atomic collision

For any player `b` satisfying

```text
quittingPunishmentValue reward b <= reward({b})(b),                (1)
```

there is a distinct player `j` such that

```text
reward({b,j})(j) >= reward({b})(j)+gamma.                           (2)
```

This conclusion is on the same literal reward table and retains the full
terminal gap.  It is obtained from an accuracy-dependent one-stage punishment
block whose deviations range over complete behavioral strategies.

### Corollary B: all four singleton rows in the maintained residual

Now specialize `I=Fin 4`, so `reward` is a quitting reward table on
`Fin 4`.  Let `bound : Real` and

```text
residual : FinFourQuantitativeFullSupportHardResidual reward bound.
```

Put

```text
gamma = residual.witness.terminalGap.
```

Then for every `b:Fin 4` there is `j!=b` such that

```text
reward({b,j})(j) >= reward({b})(j)+gamma.
```

Equivalently, after finite choice there is a fixed-point-free map

```text
next : Fin 4 -> Fin 4
```

such that

```text
reward({b,next(b)})(next(b)) >=
  reward({b})(next(b))+gamma                                       (3)
```

for every `b`.  Its finite functional graph contains a directed cycle of
length two, three, or four.  The cycle observation is bookkeeping only; the
substantive output is the four quantitative nonsingleton inequalities (3).

### Corollary C: rooted-two owner-leave handoff

With `bound`, `residual`, and `gamma` as in Corollary B, additionally let

```text
certificate : QuittingImmediateSingletonCollision reward gamma,
chain : FinFourRootedTwoNextOwnerLeaveCollisionChain
  residual certificate
```

and write `c=certificate.collider` and `s=chain.spectator`.  Then either:

1. some outsider of `{c,s}` joins the pair with gain at least `gamma`; or
2. there is `t notin {c,s}` such that

   ```text
   reward({c,s})(c)+gamma <= reward({s})(c),
   reward({s,t})(t) >= reward({s})(t)+gamma.                         (4)
   ```

Thus the collider-leave arm is followed by a terminal-gap join by a genuinely
different label:

```text
{c,s} --c leaves by gamma--> {s}
      --t joins by gamma--> {s,t}.                                  (5)
```

## Conjecture-facing change

The maintained obligation
[`FOUR_PLAYER_SINGLETON_PACKET_DISPATCH.md`](../questions/FOUR_PLAYER_SINGLETON_PACKET_DISPATCH.md)
asks for semantic use of the full-support, full-normal-core,
punishment-normal residual; singleton-matrix classifications alone are no
longer accepted progress.

This packet supplies literal nonsingleton data from that exact residual.  In
every hypothetical no-uniform table, each singleton row has a different
player whose immediate collision gain is at least the same fixed terminal
gap.  In the checked `rootedTwo_next` owner-leave chamber, the existing
collision chain therefore preserves the full gap through a source-matched
punished singleton block.

The result strictly strengthens the prior checked output

```text
rootedTwoNext_sharedHelper_or_ownerLeaveCollisionChain_or_hardHelperJoin
```

whose intermediate spectator join was only strict.  It does not yet consume
the resulting collision graph into a stationary or chronological equilibrium.

## Proof

### 1. The forced-owner barrier

Fix `b` as in Theorem A and take the pure singleton product root

```text
q=quittingPureSetRoot {b}=quittingInstantRoot b.
```

Player `b` Quits surely at this row.  The forced-owner obedience value is
`reward({b})(b)`.  If it refuses at date zero, every opponent Continues and
the continuation has mass one, so its optimized refusal cap is exactly
`quittingPunishmentValue reward b`.  Hence

```text
quittingAtomicBlockerBalance reward q b
  =reward({b})(b)-quittingPunishmentValue reward b >=0.              (6)
```

For `j!=b`, prescribed play pays `reward({b})(j)`.  Continuing at date zero
does the same, while Quitting ties the sure owner and pays
`reward({b,j})(j)`.  Therefore

```text
quittingForcedOwnerOutsiderCoordinateDefect reward q b j
  =max(0,reward({b,j})(j)-reward({b})(j)).                           (7)
```

The checked theorem

```text
QuittingTerminalExploitabilityWitness.
  terminalGap_le_atomicBlockerBarrier
```

states

```text
gamma <= max
  (quittingForcedOwnerOutsiderDefect reward q b)
  (max 0 (-quittingAtomicBlockerBalance reward q b)).                (8)
```

By (6), the second term is zero.  The outsider defect is nonnegative, so

```text
gamma <= quittingForcedOwnerOutsiderDefect reward q b.              (9)
```

The same checked file proves

```text
exists_outsider_pureEndpoint_gain_ge_of_nonneg_blockerBalance
```

and its underlying finite-attainment theorem

```text
exists_outsider_pureEndpoint_gain_ge_of_le_forcedOwnerOutsiderDefect.
```

They give `j!=b` and a pure Boolean endpoint whose gain is at least `gamma`.
At the root `q`, the Continue endpoint equals prescribed play.  Since
`gamma>0`, the attaining endpoint must be Quit.  Formula (7) is therefore
exactly (2).  This proves Theorem A.

The behavioral content of (8) is essential.  Its proof chooses a stationary
punishment row within an arbitrarily small error of the exact punishment
value, attaches it after the forced-owner row, and compares every complete
behavioral replacement.  The theorem is not a one-stage normal-form
surrogate.

### 2. Full-support adapter

For Corollary B, `residual.packet_support_eq_univ` and
`packet.mem_support_iff` give positive packet mass at every `b`.  Thus

```text
packet.positive_mass_pins_target b :
  packet.target(b)=reward({b})(b).
```

Together with `packet.punishment_le_target`, this is (1).  Apply Theorem A for
each of the four players and choose one witness `next(b)`.  Positivity of
`gamma` makes `next(b)!=b`, and finite iteration of a fixed-point-free
self-map of `Fin 4` produces a cycle of length two, three, or four.

### 3. Rooted-two third-label consequence

The field `chain.second_gap_toggle` gives either the first arm of Corollary C
directly or the collider-leave inequality

```text
reward({c,s})(c)+gamma <= reward({s})(c).                           (10)
```

In the latter case Corollary B at singleton owner `s` gives `t!=s` with

```text
reward({s,t})(t) >= reward({s})(t)+gamma.                           (11)
```

If `t=c`, equations (10)--(11) become the two opposite inequalities

```text
reward({c,s})(c)+gamma <= reward({s})(c),
reward({s})(c)+gamma <= reward({c,s})(c),
```

which contradict `gamma>0`.  Thus `t` is outside `{c,s}`, proving (4)--(5).

## Probability and behavioral-deviation audit

The root `q` is a literal independent product row with `b` quitting surely
and every other player continuing surely.  No public randomization or
cross-player correlation is introduced.  Against an outsider deviation,
the sure owner makes absorption occur at date zero, so arbitrary time
dependence collapses exactly to the two date-zero endpoints in (7).

If the owner deviates by continuing, the selected punishment continuation is
evaluated by `quittingStationaryUnilateralCap`, whose stopping-law theorem
controls every later behavioral hazard, pure time, randomization, and Never.
The atomic-blocker barrier was proved for `HasTerminalExploitabilityGap`, so
the same fixed `gamma` and the unrestricted terminal semantics of the supplied
witness are retained.

## Boundary tests

1. **Tight positive endpoint.**  At a pure singleton root, set
   `reward({b})(j)=0` and `reward({b,j})(j)=gamma`.  Then the outsider defect
   in (7) is exactly `gamma`, attained only by Quit.  This tests the constant
   and the endpoint orientation.
2. **Zero join.**  If all pair coordinates equal their singleton coordinates,
   the outsider defect is zero.  Under (1), equation (8) then rules out every
   positive terminal exploitability witness.  This is precisely the
   accuracy-dependent punished-singleton escape, not an assumed equilibrium.
3. **Punishment-normality is load-bearing.**  In a two-player local table let
   the owner receive `-1` at its singleton, `0` while absent, and no collision
   premium.  Never guarantees it zero, and opponents who Never keep its cap
   at zero, so its punishment value is zero and the atomic balance is `-1`.
   The barrier can be paid entirely by the refusal term despite zero outsider
   defect.  This is a boundary test for the source implication, not a claimed
   counterexample game.
4. **Third-label exclusion.**  In the collider-leave arm, setting `t=c` would
   require two opposite gains each at least `gamma`; adding them gives
   `2gamma<=0`.  Strict positivity is therefore exactly what forces the new
   label outside the pair.

## Source correspondence and novelty

The proof engine is checked in

```text
UniformEquilibrium/Quitting/Boundary/Repair/
  AtomicBlockerPaidGeometry.lean
```

through the atomic-blocker barrier and pure-endpoint attainment theorems.  It
is stronger than the direct punished-singleton estimate and is not claimed as
new here.  The full-support source and rooted-two chain are checked in

```text
UniformEquilibrium/Diagnostics/Quitting/Collision/SingletonPacket/
  FullSupportProjectiveQBarResidual.lean
UniformEquilibrium/Diagnostics/Quitting/Collision/SingletonPacket/
  TwoCycleLassoArmConsumers.lean.
```

The new ordinary mathematics is the same-table composition: full support pins
each packet target to its own singleton payoff, converting all four packet
floors into nonnegative atomic balances; the rooted-two collider-leave sign
then excludes reuse of the collider and forces the third-label handoff.  A
narrow search of the singleton-packet collision subtree found no existing
declaration with Theorem A or Corollaries B--C.

The generic pure-toggle theorem already gives one membership toggle at every
coalition under a terminal witness.  It does not give this result: at a
singleton it may select the owner's leave-to-Never action.  Punishment
normality and the source-matched punishment continuation are exactly what
remove that arm and force a collision by another player.

No external literature result is used.

## Actual-data adapter and downstream use

The general adapter for Theorem A is the literal inequality (1).  The Fin4
adapter is `FinFourQuantitativeFullSupportHardResidual` on the same reward
table; no equilibrium, collision graph, continuation payoff, or desired
strategy is stored in that source structure.

The immediate downstream use is Corollary C inside the checked rooted-two
owner-leave chain.  More broadly, Corollary B supplies four quantitative
nonsingleton collision rows to any future stationary, block, or
well-founded-descent consumer.  This packet does not assert that such a
consumer already exists.

## Lean handoff

A narrow formalization should first prove two simplification lemmas at
`quittingInstantRoot b`:

```text
quittingAtomicBlockerBalance_instantRoot
quittingForcedOwnerOutsiderCoordinateDefect_instantRoot
```

with right sides (6)--(7).  The main theorem then calls
`exists_outsider_pureEndpoint_gain_ge_of_nonneg_blockerBalance` and excludes
the Continue action by `witness.terminalGap_pos`.

The Fin4 corollary should derive positive mass through
`residual.packet_support_eq_univ` and `packet.mem_support_iff`, then use
`packet.positive_mass_pins_target` and `packet.punishment_le_target`.  The
rooted-two corollary should split `chain.second_gap_toggle` and discharge
`t!=c` by linear arithmetic.  Useful regressions are the four boundary tests
above.  Do not encode the selected collision map or its cycle as a source
field.

## Checked Lean realization

The generic punishment-normal collision is checked as
`QuittingTerminalExploitabilityWitness.exists_atomicCollision_gain_of_punishmentValue_le_solo`
and its normal-player adapter
`QuittingTerminalExploitabilityWitness.exists_atomicCollision_gain_of_normal`
in
`UniformEquilibrium/Quitting/Boundary/Repair/PunishmentNormalAtomicCollision.lean`.

The actual hard-residual declarations are
`FinFourQuantitativeFullSupportHardResidual.exists_terminalGap_collision_at_singleton`,
`FinFourQuantitativeFullSupportHardResidual.exists_fixedPointFree_terminalGap_collisionMap`,
and
`FinFourQuantitativeFullSupportHardResidual.ownerLeaveCollisionChain_outsiderJoin_or_thirdLabelHandoff`
in
`UniformEquilibrium/Diagnostics/Quitting/Collision/SingletonPacket/PunishmentNormalAtomicCollisionHandoff.lean`.
They preserve the residual witness's full terminal gap on the literal reward
table. The packet has `M`, `L`, `A`, and `C`, where the checked consumer is
the rooted-two third-label handoff. No theorem turns the resulting map or
leave--join chain by itself into a stationary equilibrium, Bellman path, or
uniform payoff.

## Scope and nonclaims

- The packet does not construct a stationary or chronological equilibrium
  from the four collision rows.
- It does not turn the selected functional-graph cycle into an interval-core,
  signed-influence, or strict-toggle compiler input; those require additional
  background-uniform payoff inequalities.
- It does not prove a monotone rank, payoff return, or Bellman chronology.
- Corollary C narrows only the checked rooted-two owner-leave chain.  The
  shared-helper and hard-helper-join arms require separate consumers.
- The theorem does not settle the Fin4 full-support residual or the general
  quitting-game conjecture.
