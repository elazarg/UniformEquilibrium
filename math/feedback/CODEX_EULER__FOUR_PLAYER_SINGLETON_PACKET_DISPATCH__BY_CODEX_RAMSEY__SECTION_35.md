# Review of Section 35: support-three promotion

Reviewer: `CODEX_RAMSEY`

## Claim reviewed

I independently reviewed Theorem 35.1 and Corollary 35.2 in
`notes/CODEX_EULER__FOUR_PLAYER_SINGLETON_PACKET_DISPATCH.md`.  The claim is
the exact composition, on the literal player type `Fin 4`, of

```text
QuittingTerminalExploitabilityWitness.
  supportThree_allNormal_or_cyclicSignScreen
```

with the reviewed normal terminal-gap full-support lift of Theorem 31.1.
Starting from a normalized singleton source packet of support cardinality
three and a terminal exploitability witness, the output is either a literal
full-support normalized singleton source packet for the same reward table or
the existing support-three cyclic sign screen.

## Verdict

**PASS.**  The composition, constants, source provenance, and claimed finite
complexity decrease are exact.  The result removes the unique-outsider
crossing as an independent support-three obligation.  It does not consume the
cyclic determinant screen or the full-support chamber, and it does not confuse
packet support with the recursively defined normal core.

## Checked support-three branch

The declaration in
`UniformEquilibrium/Diagnostics/Quitting/Collision/SingletonPacket/
SupportThreeNormalityDispatch.lean` has exactly the hypotheses used in the
note:

```text
witness : QuittingTerminalExploitabilityWitness reward
packet  : QuittingNormalizedSingletonSourcePacket reward
Fintype.card I=4
packet.support.card=3.
```

Its conclusion is

```text
(forall who, IsQuittingNormalPlayer reward who)
or
Nonempty (QuittingSupportThreeCyclicSignScreen packet).
```

For `I=Fin 4`, the cardinality hypothesis is literal.  The second disjunct is
exactly branch (B), with the original packet and reward table unchanged.

In the first disjunct, unfolding `IsQuittingNormalPlayer` gives precisely

```text
quittingPunishmentValue reward i
  <= reward({i})(i)
```

for every player.  No unique-outsider crossing or additional matrix
assumption survives in this arm.

## Full-support composition

The same witness supplies

```text
g=witness.terminalGap>0
```

and an unrestricted behavioral terminal exploitability gap of size `g`.
These facts and all-player normality are exactly the hypotheses of reviewed
Theorem 31.1.  With

```text
M=max_(nonempty S,i) |reward(S)(i)|,
C=1+2M(4-1)/g,
```

that theorem constructs a probability mass `mu` satisfying

```text
mu_i>=1/C>0,
sum_j mu_j reward({j})(i)>=reward({i})(i)
```

for all players.  Taking the target to be the own-singleton payoff vector
makes the solo inequalities and all positive-mass pins equalities; all-player
normality gives the punishment floors.  Thus this is literally a
`QuittingNormalizedSingletonSourcePacket reward`.  Strict positivity of every
coordinate makes its support `univ`.

The new packet is produced from the same `reward` and the same witness.  No
restriction, player reindexing, or change of table occurs.  Its support need
not equal the original support-three set; only its required full-support
conclusion is used.

The complexity named in the note is therefore honest:

```text
4-card(original support)=1,
4-card(new support)=0.
```

The construction is not iterated at full support, so this branch cannot
return to the same support-three chamber.

## Corollary and probability audit

For an arbitrary support-three packet from the analytic waist, split on the
existence of a uniform-equilibrium payoff.  In the negative branch the checked
terminal-gap equivalence supplies a terminal exploitability witness, so
Theorem 35.1 applies.  This proves the displayed finite alternative without
claiming that every packet directly decodes to a uniform payoff.

Theorem 31.1 uses stationary product roots only to construct `mu`.  Its
terminal gap and unilateral cap are quantified over all behavioral stopping
strategies, including finite pure quit times, randomization, ties, and Never.
The cyclic-screen arm is static finite sign data and is not presented as a
strategy compiler.  Section 35 inherits exactly those scopes.

## Subsumption audit

The composition is not already a checked declaration.

- `supportThree_allNormal_or_cyclicSignScreen` stops at all-player normality
  in its first arm and does not produce another packet.
- Theorem 31.1 produces a full-support packet from a normal terminal witness
  but contains no support-three sign dispatch.
- The nearby checked quantitative-root and vanishing-root declarations do not
  currently compose at their result types: the former does not expose the
  vanishing total-hazard datum required by the latter.
- `exists_uniformEquilibriumPayoff_of_normalCore_card_three` concerns the
  recursively defined LCP normal core, not the support of a normalized
  singleton packet or the set of punishment-normal players.

Thus the exact new boundary statement is the stated composition: support
three goes either to full support or to the already named internal cyclic
screen.  It removes the unique-outsider crossing from the maintained
support-three residual, while leaving both returned chambers open.
