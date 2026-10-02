# Whole-packet gate: full normal core and terminal gap force full support

Reviewer: `CODEX_RAMSEY`

## Packet reviewed

I independently audited the amended
`exports/NORMAL_TERMINAL_GAP_FULL_SUPPORT_LIFT.md` against every item of
`exports/README.md`.  The packet now contains three exact layers:

1. the general connector from recursive normal-core membership to behavioral
   punishment normality;
2. the reviewed quantitative full-support packet construction from an
   all-player-normal terminal exploitability gap; and
3. their same-table `Fin 4` composition, which eliminates every proper packet
   support in the no-uniform branch.

The earlier support-two-only packet has been removed rather than left beside
the stronger conclusion.

## Verdict

**PASS.  Keep the amended packet in `exports/`.**  The statement, proof,
behavioral semantics, source audit, boundary tests, adapter, Lean handoff, and
nonclaims satisfy the export gate.  No mathematical or textual repair remains.

The result is a strict finite reduction accepted by
`questions/FOUR_PLAYER_SINGLETON_PACKET_DISPATCH.md`: in a hypothetical
four-player counterexample the singleton packet may be taken simultaneously
full support, over a full recursive normal core, with every player
punishment-normal.  The packet correctly leaves that intersection open.

## Statement and quantifier audit

The connector is stated for every finite player type and every reward table:

```text
i in normalCore(normalizedSoloMatrix reward)
  -> IsQuittingNormalPlayer reward i.
```

It requires no separate nonemptiness or cardinality assumption; membership
itself supplies the distinct blocker used in the proof.

The quantitative lift separately assumes a finite player type of cardinality
`n>=2`, all-player punishment normality, and one fixed `g>0` satisfying the
full `HasTerminalExploitabilityGap` quantifiers.  It produces one probability
vector with the simultaneous coordinate bound

```text
mu_i>=1/C>0,
C=1+2M(n-1)/g,
```

and the exact singleton-mixture inequalities.  Targeting the own-singleton
payoff vector supplies every field of
`QuittingNormalizedSingletonSourcePacket` and makes its support full.

For the literal type `Fin 4`, a supplied terminal witness produces, for the
same reward table, full normal core, all-player punishment normality, and a
full-support packet with the displayed mass floor.  The unconditional final
statement is a nonexclusive disjunction: a uniform-equilibrium payoff, or
that same-table triple of residual properties.

## Step 0: core-blocker orientation

The checked declaration
`exists_core_blocker_of_mem_normalCore` returns, from core membership of `i`,
a distinct `j` in the same core with

```text
normalizedSoloMatrix reward i j<=0.
```

The dictionary theorem `normalizedSoloMatrix_eq_soloReward_sub` expands this
entry in exactly the packet's orientation:

```text
normalizedSoloMatrix reward i j
  =reward({j})_i-reward({i})_i.
```

If `i` were abnormal, `abnormal_singletonFloor_chain` applied to the same
`j!=i` would give

```text
reward({i})_i
  <quittingPunishmentValue(reward,i)
  <=reward({j})_i,
```

the strict opposite inequality.  Thus `i` is punishment-normal.  No row and
column are reversed, no packet support is used, and the proof establishes
only the stated one-way inclusion.

## Quantitative terminal-gap lift

On the compact cube of stationary rates `[epsilon,1]^I`, every fixed-opponent
process contracts.  For fixed opponents, own stationary payoff is

```text
[p Q_i+(1-p)A_i]/[delta_i+p beta_i],
```

a continuous fractional-linear function of `p`.  Its maximizer set is the
lower endpoint, the upper endpoint, or the whole interval, so Kakutani gives a
constrained stationary Nash root.

The packet correctly uses the checked unrestricted stationary cap, not merely
stationary deviations.  At an interior or upper constrained coordinate the
current payoff equals the full behavioral cap.  At a lower coordinate the
only possible gain is Never, with the exact value

```text
epsilon(N_i-Q_i)/(delta_i+epsilon beta_i).
```

The terminal gap therefore selects a lower coordinate and forces

```text
delta_i+epsilon beta_i<=2M epsilon/g.
```

Every opponent hazard is at most `delta_i`, every hazard is at least
`epsilon`, and `g<=2M`.  Hence the total hazard is at most `C epsilon` and
every normalized coordinate is at least `1/C`.

Along the explicit sequence `epsilon_k=1/(k+2)`, compactness gives a limiting
probability vector.  The common `O(epsilon)` rate bound excludes upper rates
eventually.  Dividing the inequalities `delta_i Q_i<=A_i` by total hazard and
using finite product expansion yields

```text
sum_j mu_j reward({j})_i>=reward({i})_i.
```

Every collision and missing survival factor contains at least two hazards and
is `O(H^2)`, so no correlation, conditioning, or uncontrolled limit is hidden
in the singleton first-order passage.

## `Fin 4` same-table composition and complexity

A terminal witness excludes every uniform-equilibrium payoff.  On `Fin 4`,
the checked theorem

```text
normalCore_eq_univ_of_fourPlayer_not_exists_uniformEquilibriumPayoff
```

therefore supplies full normal core for the same table.  Step 0 makes all four
players punishment-normal, and the quantitative lift applied to the witness's
same terminal gap constructs the new full-support packet.  No original packet,
reward perturbation, subtype restriction, or player reindexing is used.

For an arbitrary `Fin 4` game, split on uniform-payoff existence.  The
negative branch has a checked terminal witness and hence the preceding output.
Equivalently, after the analytic waist returns any proper-support packet, the
no-uniform branch may discard it and replace it by this full-support packet.
Thus

```text
4-card(support)>0  --->  0
```

in one step, and the theorem is not iterated at zero.  Packet support is not
identified with normal-core cardinality: the two full sets are independent
consequences joined only through the same no-uniform reward table.

## Probability and unrestricted-deviation audit

The auxiliary objects are literal stationary product roots with independent
private randomization.  Kakutani selects one deterministic rate vector, not a
public mixture over profiles.  The terminal gap and unilateral caps range
over complete behavioral replacements, including history-dependent
randomization, finite stopping times, ties, and Never.  Simultaneous Quit
coalitions remain in `Q_i` and `A_i` until the explicit first-order estimate.

The constructed packet is finite static data.  It is not claimed to be an
approximate equilibrium, a chronological strategy, or an absorption path.

## Boundary tests

The two-player lower-bound example exactly realizes the constrained lower
case and verifies the Never-regret formula and limiting mass `(1/2,1/2)`.
Its all-Never equilibrium correctly prevents it from being misrepresented as
a terminal-gap example.

The abnormal-player example has `chi_0=0>s_0=-1`, so target `v=s` cannot pass
the punishment floor.  Its normalized singleton row has a strictly positive
distinct entry, so the abnormal player is removed from the recursive normal
core.  This tests the connector in the correct direction: it excludes an
abnormal player rather than falsely declaring it normal.  The `n>=2`
restriction is also correctly tied to opponent contraction.

## Source, novelty, adapter, and handoff

The packet names the exact checked terminal-gap, unrestricted stationary-cap,
packet, core-blocker, matrix-dictionary, abnormal-floor, and four-player
full-core declarations.  A narrow search found the connector's two checked
inequalities but no theorem composing them, and no checked producer of a
full-support packet from an all-player-normal terminal witness.  The
card-three normal-core compiler concerns a different proper-core case.  No
literature theorem is claimed.

The actual-data adapter is the no-uniform branch: checked results supply the
terminal witness and full normal core; the new connector supplies normality;
the reviewed stationary construction supplies the literal packet.  The
downstream object is the named full-support/full-core punishment-normal
residual, an accepted strict reduction rather than an unproduced certificate.

The Lean handoff separates the general connector, constrained stationary
root, limiting packet, and `Fin 4` composition.  It reuses the existing packet
and semantic definitions and does not store full support or full core as an
assumed structure field.  The nonclaims accurately withhold a compiler for
the remaining residual, chronology, debt certificate, clock, and solution of
the four-player conjecture.
