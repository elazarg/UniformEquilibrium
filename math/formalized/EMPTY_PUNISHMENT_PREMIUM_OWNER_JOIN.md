# Empty punishment premium forces an owner join

Authors: CODEX_EULER

Independent component review:
[CODEX_RAMSEY](../feedback/CODEX_EULER__FOUR_PLAYER_SINGLETON_PACKET_DISPATCH__BY_CODEX_RAMSEY__SECTION_28_4.md)

## Exact statement

Let `I` be a four-element player set, let a finite quitting reward table be
fixed, and suppose there is a `QuittingTerminalExploitabilityWitness`.  Fix a
player `d` and write

```text
s_d=r_{d}(d),
chi_d=quittingPunishmentValue reward d.
```

Assume the strict empty-cell owner premium

```text
s_d<chi_d.                                             (1)
```

Then

```text
s_d<0,                       chi_d<=0,                 (2)
```

and there is a nonempty coalition `T subset I\{d}` such that

```text
r_T(d)<r_(T union {d})(d).                            (3)
```

Put `P=T union {d}`.  At least one of the following finite outputs holds:

1. `P` is an exact sure-exit set and `r_P` is a uniform-equilibrium payoff
   against unrestricted behavioral deviations;
2. some old member `z in T` strictly prefers to leave `P`:

   ```text
   r_P(z)<hat_r_(P\{z})(z);                           (4)
   ```

3. some outsider `z notin P` strictly prefers to join `P`:

   ```text
   r_P(z)<r_(P union {z})(z).                         (5)
   ```

Here `hat_r_empty=0`, though `P\{z}` is nonempty whenever `d` remains.  Under
the terminal exploitability witness the sure-exit output is excluded.  Thus
the abstract premium (1) is replaced by one of seven nonempty opponent-
coalition joins by `d`, followed by a strict toggle whose responsible label
is not `d`.

## Conjecture-facing change

The maintained obligation is
[`FOUR_PLAYER_SINGLETON_PACKET_DISPATCH.md`](../questions/FOUR_PLAYER_SINGLETON_PACKET_DISPATCH.md).
The accepted packet
[`REPAIRED_RESIDUAL_PURE_EXIT_DESCENT.md`](REPAIRED_RESIDUAL_PURE_EXIT_DESCENT.md)
reduces a positive repaired owner-floor residual to a nonempty pure-exit test
or to exactly the empty punishment premium (1).

This theorem removes that exceptional arm.  It converts the semantic scalar
`chi_d` into finite reward-table data using a checked four-player player-
deletion obstruction, and then enters the checked anchored sure-exit
promotion.  The result is either an existing all-behavior compiler output or
the explicit finite toggles (4)--(5).  No generic cycle collector is used.

## Definitions and assumptions

The punishment value is the infimum, over all opponent behavioral profiles,
of player `d`'s unrestricted behavioral best-response value.  The proof does
not assume the infimum is attained and does not select a punishment strategy.

The pure empty opponent row means all opponents Continue at date zero.  Its
unilateral cap for `d` is `max(s_d,0)`, accounting for immediate solo Quit and
Never.  The coalition `P` in the output is a deterministic pure exit set.  If
it is sure-exit, the checked stationary consumer covers arbitrary behavioral
stopping times and Never, not only membership deviations or bounded
controllers.  There is no randomization or public correlation in the finite
output.

## Source correspondence

The actual-data source is the empty branch (7) of the accepted
`REPAIRED_RESIDUAL_PURE_EXIT_DESCENT` packet.  Its four-player provenance is
the checked semantic dispatch
`hasQuittingStrictToggleSemanticDispatch_of_card_four` in
`UniformEquilibrium/Diagnostics/Quitting/Collision/Toggles/StrictToggleSemanticDispatch.lean`.

The exact checked declarations consumed here are:

- `quittingPunishmentValue_le_pureRowCap` in
  `UniformEquilibrium/Quitting/Punishment/ContinueFloor.lean`;
- `QuittingTerminalExploitabilityWitness.exists_strict_owner_toggle_of_card_eq_four`
  in `UniformEquilibrium/Diagnostics/Quitting/Collision/ThreeRoleSpectator.lean`;
- `isQuittingSureExitSet_insert_or_oldLeave_or_otherJoin` in
  `UniformEquilibrium/Quitting/Paths/AnchoredJoinPromotion.lean`; and
- `isUniformEquilibriumPayoff_setReward_of_isQuittingSureExitSet` in
  `UniformEquilibrium/Quitting/Paths/SureExitSet.lean`.

The strict-owner-toggle theorem already combines exact player deletion with
unconditional three-player existence.  What is new here is the source
adapter: (1) automatically supplies its nonpositive-punishment hypothesis via
the empty pure-row cap, and its output is immediately promoted to the exact
finite alternatives above.  No paper theorem is used.

## Proof

Apply `quittingPunishmentValue_le_pureRowCap` to the empty coalition.  Since
joining the empty set means quitting solo and erasing from it remains Never,
the result is

```text
chi_d<=max(s_d,0).                                    (6)
```

If `0<=s_d`, then the right side of (6) is `s_d`, contradicting (1).
Therefore `s_d<0`, after which (6) gives `chi_d<=0`.  This proves (2).

The hypotheses (1), (2), cardinality four, and the terminal witness are
exactly those of
`QuittingTerminalExploitabilityWitness.exists_strict_owner_toggle_of_card_eq_four`.
It returns a nonempty `T`, with `d notin T`, satisfying (3).

Apply `isQuittingSureExitSet_insert_or_oldLeave_or_otherJoin` to the strict
join `T -> T union {d}`.  Its alternatives are precisely: the enlarged set
is sure-exit; an old member of `T` strictly leaves; or a different outsider
strictly joins.  The anchored entrant `d` cannot be the leaving witness, and
the outsider witness lies outside `P`, so neither residual toggle is assigned
to `d`.  In the sure-exit branch, the checked consumer gives the stated
uniform payoff.  This completes the proof.

## Boundary tests

The strictness in (1) is essential.  If every reward coordinate is zero, then
`s_d=chi_d=0` and no strict owner join need exist.

The negative/nonpositive conclusion is sharp.  Give `d` payoff zero at every
coalition excluding it, payoff `-1` at `{d}`, payoff `1` at one coalition
`T union {d}`, and arbitrary bounded values at its other joined coalitions.
Never guarantees zero, while the all-Continue opponent row caps `d` at zero,
so `chi_d=0>s_d=-1`.  The coalition `T` supplies the strict join (3).

Both promotion branches are real.  Keeping the preceding `d` coordinates,
choose the other players' payoffs so that every member of `P=T union {d}`
weakly prefers to remain and every outsider weakly prefers to remain out;
then `P` is sure-exit.  Changing only one old member's payoff after leaving
to be strictly larger gives (4).  Changing only one outside player's joined
payoff to be strictly larger gives (5).  These changes do not alter (1)--(3).

## Adapter and consumer

The adapter reads `d,s_d,chi_d` from the empty premium returned by the
accepted repaired-residual packet.  It applies the empty pure-row cap, invokes
the checked card-four owner-toggle theorem, and tests the one enlarged
coalition with the checked anchored promotion.  The possible `T` are exactly
the seven nonempty subsets of the other three players.

The positive branch invokes the checked sure-exit all-behavior consumer.
The negative branches return the strict finite reward inequalities (4)--(5),
which are a smaller residual accepted by the maintained question.

## Lean handoff

The theorem should take a terminal exploitability witness, a proof that the
player type has cardinality four, a label `d`, and (1).  Instantiate
`quittingPunishmentValue_le_pureRowCap reward d empty`, simplify
`quittingSetReward` at the empty and singleton sets, and derive (2) by cases on
`0<=s_d`.

Pass (1) and `chi_d<=0` directly to
`witness.exists_strict_owner_toggle_of_card_eq_four`.  Feed its returned join
to `isQuittingSureExitSet_insert_or_oldLeave_or_otherJoin`; in the positive
branch invoke the sure-exit consumer.  No new structure should carry the
desired join or sure-exit conclusion as an assumption.

## Scope and nonclaims

This packet removes only the strict empty punishment premium.  It does not
consume the subsequent different-label toggles, prove that their iteration
terminates, or assemble a chronology.  It does not apply without a terminal
exploitability witness or without the exact four-player cardinality needed to
exclude the deletion branch by three-player existence.

The theorem does not construct or attain a punishment strategy.  Its only
unrestricted-strategy conclusion is supplied by the checked sure-exit
consumer.
