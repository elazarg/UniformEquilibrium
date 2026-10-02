# A quantitative leave--join chain produces a two-debtor stationary source

Author: `CODEX_EULER`

Independent falsification review:
[`CODEX_RAMSEY`](../feedback/CODEX_EULER__FIN4_SEARCH_SPACE_INVENTORY__BY_CODEX_RAMSEY__SECTION_16.md)

## Exact statement

Let the player type be literally `Fin 4`, let

```text
reward : {S : Finset (Fin 4) // S.Nonempty} -> Payoff (Fin 4)
```

be a quitting reward table, and let `M>=0` satisfy

```text
|reward(S)(i)| <= M
```

for every nonempty coalition `S` and player `i`.  Let

```text
witness : QuittingTerminalExploitabilityWitness reward,
gamma = witness.terminalGap > 0.
```

Fix four distinct labels `c,s,t,o` satisfying

```text
reward({c,s})(c)+gamma <= reward({s})(c),             (1)
reward({s})(t)+gamma <= reward({s,t})(t).             (2)
```

Consider the binary normal-form game of players `c` and `t` in which `s` is
forced to Quit and `o` is forced to Continue.  Choose a mixed Nash equilibrium
of that game, with Quit probabilities `x` for `c` and `y` for `t`, and form
the independent product root

```text
q_s=1, q_o=0, q_c=x, q_t=y.                           (3)
```

Let `sigma` be the stationary behavioral profile repeating `q`, and let
`(U,B)` be its terminal-semantic pair, where `B` is the unrestricted
behavioral best-response envelope.  Put

```text
alpha=gamma/(gamma+2M).
```

Then:

1. `0<alpha<=1` and `y>=alpha`.
2. The terminal law of `sigma` assigns total mass `y` to coalitions
   containing `{s,t}`.  More exactly,

   ```text
   Prob({s,t})=(1-x)y,
   Prob({c,s,t})=xy,
   ```

   so one of these two literal atoms has mass at least `alpha/2`.
3. The two solved players have zero unrestricted debt and are punishment-floor
   safe:

   ```text
   B_c=U_c, B_t=U_t,
   quittingPunishmentValue reward c <= U_c,
   quittingPunishmentValue reward t <= U_t.          (4)
   ```

4. There is `w in {s,o}` with

   ```text
   B_w-U_w >= gamma.                                  (5)
   ```

   Thus the positive-debt support of this actual carrier pair is a nonempty
   subset of `{s,o}` and has cardinality at most two.
5. The same `w` is the observer of a literal paid source on the actual
   stationary profile:

   ```text
   Nonempty (QuittingPaidFirstDisagreementRow reward sigma w gamma).  (6)
   ```

## Conjecture-facing change

The checked rooted-two owner-leave chain previously ended with the static
gap path

```text
{c,s} --c leaves--> {s} --t joins--> {s,t}.
```

This packet consumes that exact arm into an executable stationary profile on
the same reward table.  The new joiner has a fixed positive hazard, the
profile retains a fixed pair-or-triple terminal atom, two players are solved
against every behavioral deviation and lie above punishment, and all
terminal exploitability is localized to the other two labels as an exact
paid first-disagreement row.

This is a strict semantic narrowing of the owner-leave arm in
[`FOUR_PLAYER_SINGLETON_PACKET_DISPATCH.md`](../questions/FOUR_PLAYER_SINGLETON_PACKET_DISPATCH.md).
It does not consume the paid row into a Bellman return or a uniform payoff.

## Constructive two-by-two Nash selection

For the constrained game, let

```text
Delta_c(y)=payoff_c(Quit against y)-payoff_c(Continue against y),
Delta_t(x)=payoff_t(Quit against x)-payoff_t(Continue against x).
```

Both functions are affine.  Equations (1)--(2) give

```text
Delta_c(0)<=-gamma<0,
Delta_t(0)>= gamma>0.                                (7)
```

A mixed Nash equilibrium exists by the following exhaustive elementary
construction, so no unproved selection lemma is deferred.

- If `Delta_c(1)<=0`, take `x=0,y=1`.
- If `Delta_c(1)>0` and `Delta_t(1)>=0`, take `x=1,y=1`.
- If `Delta_c(1)>0` and `Delta_t(1)<0`, affineness and (7) give unique
  interior zeros `Delta_c(y)=0` and `Delta_t(x)=0`; take those `x,y`.

In every case each positive-probability pure action is a best response, and
the unused endpoint has the correct weak inequality.  These are all possible
sign cases after (7).

## Quantitative hazard and atom proof

At `y=0`, (1) gives

```text
Delta_c(0)=reward({c,s})(c)-reward({s})(c)<=-gamma.   (8)
```

At `y=1`, boundedness gives

```text
Delta_c(1)=reward({c,s,t})(c)-reward({s,t})(c)<=2M.  (9)
```

Therefore

```text
Delta_c(y)
  =(1-y)Delta_c(0)+y Delta_c(1)
  <= -(1-y)gamma+2My.                               (10)
```

If `x>0`, Nash optimality of the Quit action gives `Delta_c(y)>=0`, and
(10) gives

```text
y>=gamma/(gamma+2M)=alpha.                          (11)
```

If `x=0`, player `t` faces `c` continuing surely, so (2) makes Quit strictly
better by at least `gamma`; Nash optimality forces `y=1`, and (11) again
holds.  Equation (2) and the reward bound imply `gamma<=2M`, so the
denominator is positive and `0<alpha<=1`.

Player `s` quits surely and `o` continues surely.  On the event that `t`
Quits, the only remaining random action is `c`'s.  Independence gives the two
masses in item 2; their sum is `y>=alpha`, so their maximum is at least
`alpha/2`.

## Unrestricted-deviation and floor proof

Against any unilateral behavioral deviation by `c` or `t`, the opponent
`s` still Quits surely at date zero.  The game absorbs before any later
history can be reached.  The deviator's payoff therefore depends only on its
date-zero Boolean marginal, and the constrained mixed-Nash inequalities
control every such marginal.  Consequently the prescribed payoff equals the
full behavioral cap in both solved coordinates:

```text
B_c=U_c, B_t=U_t.                                    (12)
```

Equivalently, first use the stationary semantic identity

```text
quittingTerminalSemanticPair_stationary_envelope_eq_cap
```

and then the surely-absorbing one-stage Nash calculation.  The checked
inequality

```text
quittingPunishmentValue_le_stationaryUnilateralCap
```

turns (12) into the two punishment floors in (4).

Apply `witness.terminalExploitability` to the literal profile `sigma`.  It
selects a player with an unrestricted behavioral deviation gain at least
`gamma`.  Equation (12) excludes `c` and `t`; since the four labels are
distinct and exhaustive, the selected player `w` lies in `{s,o}` and (5)
holds.

Rewrite `B_w` as `quittingStationaryUnilateralCap reward q w` using
`quittingTerminalSemanticPair_stationary_envelope_eq_cap`.  The checked
stationary decoder

```text
exists_oriented_quitNow_never_gap_of_stationary_cap_debt
```

then produces an oriented payoff difference of at least `gamma` between
immediate Quit and Never.  Applying

```text
exists_quittingPaidFirstDisagreementRow_of_pureTimePayoff_sub
```

gives (6) with the same opponents, observer, source profile, and terminal
law.

## Probability and behavioral semantics

The only randomization is the independent private date-zero mixing `x,y` of
players `c,t`.  There is no public correlation.  Since `s` Quits surely, the
prescribed stationary profile absorbs at date zero with probability one.

The zero-debt statements are not stationary-regret claims: they quantify all
behavioral deviations and reduce them to their date-zero marginal because an
unchanged sure opponent absorbs the deviated process immediately.  The paid
row retains two deterministic Quit-time/Never witnesses against the actual
opponents and their actual reach probability.

## Actual-data adapter and downstream source

The actual Fin4 adapter is the reviewed theorem exported in
[`FIN4_PUNISHMENT_NORMAL_ATOMIC_COLLISION_HANDOFF.md`](FIN4_PUNISHMENT_NORMAL_ATOMIC_COLLISION_HANDOFF.md).
In its rooted-two collider-leave arm, take `c` to be the collider, `s` the
chain spectator, and `t` the guaranteed third-label joiner.  These labels are
distinct, and the unique remaining Fin4 label is `o`.  Inequalities (1)--(2)
are the literal same-table outputs of that adapter.

The downstream object is exactly `QuittingPaidFirstDisagreementRow`, the
maintained behavioral source type used by the paid-return route.  The packet
also supplies the stronger provenance fields of a stationary source, two
zero-debt floor-safe coordinates, and a fixed nonsingleton terminal atom.
No checked theorem currently turns these fields alone into a return or a
uniform payoff.

## Boundary tests

1. **Sharp hazard constant.**  Take endpoint differences
   `Delta_c(0)=-gamma`, `Delta_c(1)=2M`,
   `Delta_t(0)>0`, and `Delta_t(1)<0`.  The interior equilibrium has
   `y=gamma/(gamma+2M)`, so the constant in item 1 cannot be improved from
   only (1) and boundedness.
2. **Pure boundary.**  If `Delta_c(1)<=0`, the selected equilibrium is
   `x=0,y=1`.  This checks that the argument does not divide by an interior
   mixing probability.
3. **Atom split.**  At `x=1/2`, the two atoms in item 2 each have mass
   `y/2`; the pigeonhole factor `1/2` is sharp.
4. **The fourth label is genuinely unsolved.**  Keep all `c,s,t` coordinates
   fixed and let player `o` receive zero when it Continues and one whenever
   it joins the date-zero terminal coalition.  Then its prescribed payoff is
   zero and immediate Quit gains one, while the constrained `c,t` Nash and
   the hazard/atom conclusions are unchanged.  Thus the theorem cannot call
   `sigma` a Nash profile or delete `o` from the debt support.
5. **Sure absorption is load-bearing.**  If `s` merely Quits with probability
   below one, a deviation by `c` or `t` can reach later histories.  The finite
   date-zero Nash inequalities no longer imply zero unrestricted debt.

## Source and subsumption audit

The all-behavior semantic identities and decoder are checked in

```text
UniformEquilibrium/Diagnostics/Quitting/Collision/Toggles/
  LargeBaseStationarySemanticHandoff.lean
UniformEquilibrium/Quitting/Stationary/MinMax.lean
UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticNegativeVertexGerm.lean
UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticPaidFirstDisagreement.lean.
```

The same-table rooted-two source is checked through

```text
UniformEquilibrium/Diagnostics/Quitting/Collision/SingletonPacket/
  TwoCycleLassoArmConsumers.lean
```

and the independently reviewed atomic-collision composition cited in the
adapter section.

The checked `exists_largeBasePaidStationaryHandoff` also produces a
stationary paid row, but from a different source and with different retained
data: it solves a full three-free-player game and repairs a singleton owner,
whereas this theorem preserves the rooted-two leave--join labels, forces a
quantitative joiner hazard, and retains a fixed pair/triple atom.  Neither
theorem subsumes the other.  A narrow search found no checked declaration
with this constrained Nash localization.

No external literature theorem beyond the elementary finite two-by-two Nash
calculation proved above is used.

## Lean handoff

1. Define the induced two-player endpoint differences with `s` fixed at
   `PMF.pure true` and `o` at `PMF.pure false`.  Prove the three-case
   two-by-two Nash selector directly, avoiding a new general game structure.
2. Package `x,y` as Boolean PMFs and define `q`.  Expand `c`'s endpoint
   difference at `y=0,1`; linear arithmetic proves the `alpha` bound.
3. Compute the two coalition masses by `pmfPi` independence and pigeonhole
   their sum.
4. Use sure-opponent absorption to identify the full behavioral caps of
   `c,t` with their one-stage Nash values, then invoke
   `quittingTerminalSemanticPair_stationary_envelope_eq_cap` and
   `quittingPunishmentValue_le_stationaryUnilateralCap`.
5. Apply the terminal witness, exclude `c,t`, rewrite the selected envelope
   as the stationary cap, and use the two paid decoder declarations named
   above.

Useful regressions are the five boundary tests.  Do not store the selected
Nash point, debtor, paid row, or atom as an input source field.

## Checked Lean realization

The quantitative stationary object is
`FinFourLeaveJoinStationaryTwoDebtorHandoff`, constructed by
`nonempty_finFourLeaveJoinStationaryTwoDebtorHandoff` in
`UniformEquilibrium/Diagnostics/Quitting/Collision/SingletonPacket/LeaveJoinStationaryTwoDebtorHandoff.lean`.
Its fields retain the hazard lower bound, pair/triple atom alternative, two
all-behavior zero-debt and punishment-floor-safe coordinates, nonempty debt
support of cardinality at most two, a terminal-gap debtor, and a literal
`QuittingPaidFirstDisagreementRow` on the actual stationary profile.

The same file's
`FinFourQuantitativeFullSupportHardResidual.ownerLeaveCollisionChain_outsiderJoin_or_stationaryTwoDebtorHandoff`
is the actual residual adapter: it either keeps the enlarged-pair outsider
join or constructs this handoff from the collider-leave/third-label-join arm.
The result has `M`, `L`, and `A`. It does not have `C`: no checked theorem
turns this paid row and two-debtor source into a Bellman return, payoff near-
return, terminal approximate Nash profile, or uniform-equilibrium payoff.

## Scope and nonclaims

- The packet does not construct an exact Nash--Bellman edge, cyclic block,
  floor-safe stack, payoff return, terminal approximate Nash profile, or
  uniform-equilibrium payoff.
- It does not solve the shared-helper, direct pair-to-triple, or hard-helper
  arms of the rooted-two dispatch.
- Only `c,t` are proved punishment-floor safe.  The sure owner `s` and fourth
  label `o` may lie below punishment.
- The fixed atom is behavioral terminal-law mass, not Bellman charge or a
  source-matched connector to the minimum plateau.
- The paid row is a source for the maintained paid-return problem, not its
  consumer.
