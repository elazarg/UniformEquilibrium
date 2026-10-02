# Review of Section 36: full normal core implies punishment normality

Reviewer: `CODEX_RAMSEY`

## Claim reviewed

I independently reviewed Lemma 36.1, Theorem 36.2, and Corollary 36.3 in
`notes/CODEX_EULER__FOUR_PLAYER_SINGLETON_PACKET_DISPATCH.md`.

The new connector is

```text
i in normalCore(normalizedSoloMatrix reward)
  -> IsQuittingNormalPlayer reward i.
```

It is then composed, on `Fin 4`, with the checked full-normal-core theorem and
the independently reviewed normal terminal-gap lift to show that a terminal
counterexample witness produces a full-support normalized singleton source
packet.  Consequently the analytic packet frontier may be restricted to full
support; every proper support is bypassed in the no-uniform branch.

## Verdict

**PASS.**  The matrix orientation, abnormal-player contradiction, same-table
composition, quantitative mass floor, and finite support decrease all check.
No hidden nonemptiness, cardinality, principal-heredity, or stationary-
completeness assumption occurs.  Section 36 strictly supersedes Section 35 as
the support-cardinality frontier statement.

One harmless wording improvement is to read Corollary 36.3 as “at least one
of the following two alternatives” rather than an exclusive “exactly one”:
a game may conceivably have both a uniform payoff and a full-support packet.
The proof and displayed disjunction already use the nonexclusive meaning.

## Core-blocker orientation

The checked declaration

```text
exists_core_blocker_of_mem_normalCore
```

in `UniformEquilibrium/Quitting/Classification/LCP/NormalCore.lean` says that
from `i in normalCore M` one obtains a player `j` in the same core with

```text
j != i,
M i j <= 0.                                           (R1)
```

For `M=normalizedSoloMatrix reward`, the exact bridge

```text
normalizedSoloMatrix_eq_soloReward_sub reward i j
```

in `Quitting/Classification/PreemptionGateDictionary.lean` expands the row
and column in the required orientation:

```text
M i j
 =quittingSoloReward reward j i
  -quittingSoloReward reward i i.                    (R2)
```

Thus (R1) says that singleton owner `j` pays recipient `i` no more than
`i`'s own singleton row does.  This is exactly (36.3); the indices are not
reversed.

If `i` were not punishment-normal, linear order turns that negation into
`IsQuittingAbnormalPlayer reward i`.  The checked
`abnormal_singletonFloor_chain reward` applied to `j != i` gives

```text
solo(i,i) < punishmentValue(i) <= solo(j,i),          (R3)
```

contradicting (R1)--(R2).  Hence core membership implies punishment
normality.  Membership itself supplies the distinct blocker, so Lemma 36.1
does not need a separate global `[Nonempty I]` assumption.

The resulting inclusion is one-way:

```text
normalCore(normalizedSoloMatrix reward)
  subset punishmentNormalPlayers reward.
```

No converse is used or claimed.

## Four-player terminal-witness composition

For `I=Fin 4`, the witness's checked
`not_exists_uniformEquilibriumPayoff` field supplies the negative hypothesis
to

```text
normalCore_eq_univ_of_fourPlayer_not_exists_uniformEquilibriumPayoff.
```

The theorem's `[Nonempty I]` and `Fintype.card I=4` inputs are automatic for
the literal type `Fin 4`.  Its conclusion is full recursive normal core for
the same reward table.  Lemma 36.1 therefore makes every one of the four
players punishment-normal.

The reviewed Theorem 31.1 now applies to the same terminal witness with

```text
g=witness.terminalGap>0,
M=max_(nonempty S,i) |reward(S)(i)|,
C=1+2M(4-1)/g.
```

It returns a normalized singleton source packet for the same table with

```text
mass(i)>=1/C>0
```

for every player.  Hence its support is literally `univ`.  The stationary
product roots in Theorem 31.1 are only its finite packet construction;
terminal exploitability and the unilateral cap quantify over unrestricted
behavioral strategies, including finite quit times, randomization, and Never.

## Analytic-waist and complexity audit

Apply `quittingGame_uniformPayoff_or_normalizedSingletonSourcePacket`.  Its
uniform-payoff arm is already accepted.  In its packet arm, split on whether a
uniform payoff exists.  If not, the checked terminal-gap equivalence supplies
a witness and Theorem 36.2 constructs a new full-support packet.  The support
of the originally returned packet is irrelevant; no data are silently copied
from it.

Thus, in the no-uniform branch, the finite complexity

```text
4-card(packet.support)
```

is replaced by zero whenever the original support is proper.  The construction
is not reapplied at full support, so the transition cannot cycle.  The result
does not identify packet support with normal-core cardinality: full normal
core is a separate checked consequence of the same no-uniform hypothesis and
is used only to obtain punishment normality.

## Subsumption and remaining scope

A narrow source search found the two halves but not their connector.

- `normalCore_eq_univ_of_fourPlayer_not_exists_uniformEquilibriumPayoff`
  stops at recursive-core equality.
- `abnormal_singletonFloor_chain` supplies the opposing strict singleton
  inequality but does not mention the core blocker.
- `supportThree_allNormal_or_cyclicSignScreen` and the support-two crossed
  machinery are no longer needed to produce full support under a terminal
  witness.
- The nearby checked normal-terminal-gap root theorem still does not expose
  the total-hazard convergence input needed by the checked vanishing-root
  packet theorem; reviewed Theorem 31.1 remains the packet producer.
- The checked card-three normal-core theorem concerns a different, proper
  recursive core and is not used.

The theorem removes every proper packet-support obligation but does not
consume the resulting full-support chamber, prove the four-player conjecture,
or infer any principal Standard-Q property.  In a hypothetical counterexample
the remaining packet is full support and the same table independently has
full normal core and punishment-normal residual-hard data.
