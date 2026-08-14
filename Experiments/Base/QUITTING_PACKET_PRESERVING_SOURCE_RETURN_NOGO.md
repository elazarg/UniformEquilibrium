# Packet-preserving source return is impossible

## Verdict

The literal theorem is false.

A localized positive actual-row deviation cannot occur as a row of an exact
Nash--Bellman chronology while its source root and shifted tail are both kept
fixed. This already fails before debt descent, return charge, or terminal
compilation is considered. Keeping the source profile, terminal coalition,
and its positive mass adds constraints and therefore cannot restore the
coupling.

The general root--tail no-go is in
`UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticLiteralSourceReturnNoGo.lean`.
Its positive-collision stopping-law adapter is in
`Experiments/quitting/PacketPreservingSourceReturnNoGo.lean`.

## The invariant

Fix a literal reached row, a player `i`, and the literal continuation payoff.
Write

```text
Q = payoff if i Quits,
C = payoff if i Continues,
q = prescribed Quit probability,
c = prescribed Continue probability,
D = Q - C.
```

The coordinate Nash defect is

```text
delta = max(Q,C) - (q Q + c C).
```

Equivalently, it is the support-weighted complementarity residual

```text
delta = c D       when D >= 0,
delta = -q D      when D <= 0.
```

For the canonical legal deviation which changes only player `i` at this row
to the better pure endpoint and then resumes the same tail, the exact global
gain is

```text
G = liveMass * delta.
```

This is not an estimate. It is an identity on the literal behavioral source.
The localized packet has `G > 0`, hence `delta > 0`.

An exact Nash--Bellman edge on the same root--tail fiber satisfies the two
endpoint complementarity inequalities

```text
c D <= 0,
0 <= q D.
```

Together with `q,c >= 0` and `q+c=1`, they force `delta=0`. Thus the exact
Nash--Bellman graph and the positive-packet graph have empty intersection on
every fixed root--tail fiber:

```text
literal root + literal tail + G > 0
                    ==> no exact Nash--Bellman edge.
```

This scalar `delta`, not a missing compactness or selection argument, is the
exact invariant preventing the coupling.

## What is literally retained

`QuittingLiteralPositiveActualRowPacket` stores:

- the original behavioral source profile;
- the marked causal date and deviating player;
- the original terminal coalition;
- that coalition's literal stage mass, with a proof that it is positive; and
- the canonical actual-row best-endpoint gain, with a proof that it is
  positive.

`IsLiteralNashBellmanEmbedding` asks only for the source payoff, root, and next
continuation payoff to agree with this packet. Even this weaker embedding is
impossible. Therefore an embedding retaining the entire source prefix and
behavioral tail is impossible a fortiori. The chronology theorem says that
the packet cannot occur at any date of an exact Nash--Bellman chronology.

The stopping-law instantiation uses
`positiveCollisionMarkedTailDispatch_fixedOtherLegalDeviation`. It retains
the selected target source, marked date, fixed non-observer, terminal
coalition, and the same positive coalition mass, packages every selected row,
and proves directly that no package has a literal exact source return. There
is no additional sign selection or case split in the conclusion.

## Why the terminal coalition and mass cannot help

The marked coalition mass is useful for proving that the row is reached and
for obtaining the uniform lower bound on `G`. But Nash complementarity is a
conditional root--tail condition. Once the root and tail are frozen, the
coalition label and its exterior reach probability cannot change `delta`.
They only multiply or witness a residual which exact Nash requires to vanish.

In the sure-observer rows used by the positive-collision frontier, the point
is sharper: for every distinct player the current suffix debt equals the
actual coordinate defect. Hence the positive strategic source is itself a
positive-debt, non-Nash row. Declaring it exact would not return that source;
it would erase the very debt and deviation being transported.

## The apparent suffix loophole

One may keep the non-Nash packet row as a prefix and attach an exact chronology
only after it. That operation is possible in principle, but it is not an exact
Nash--Bellman chronology through the source row. If the literal tail is kept,
the same deviation and the same gain `G` remain.

Lean proves the quantitative forms:

```text
literal root-tail epsilon-Nash  ==>  G <= epsilon,
epsilon < G                    ==>  source is not terminal epsilon-Nash.
```

So an attached exact suffix cannot turn the unchanged source into a terminal
approximate equilibrium at errors below the packet gain. On the selected
frontier subsequence that gain already has the uniform lower bound supplied by
the localization theorem.

This does not rule out using the non-Nash row as a **charged interface** and
paying its residual elsewhere. It rules out calling that interface exact, or
obtaining exactness for free from a later return.

## Consequence for the proof search

The old literal source-return obligation should be retired. Any viable repair
must relax at least one of the following:

1. change the root, thereby changing the played packet and generally its
   coalition law;
2. change the continuation payoff/tail, thereby paying a seam mismatch;
3. allow Nash error at least the retained actual gain; or
4. keep the source row non-Nash and explicitly charge its complementarity
   residual in a larger debt/return account.

The useful replacement question is therefore not whether the positive packet
can be embedded unchanged into an exact chronology. It cannot. The remaining
question is whether its fixed positive residual can fund a controlled root or
tail move whose loss of packet data is quantitatively recoverable, or can be
balanced by a genuinely state-matched charged return.

## Lean declarations

The principal declarations are:

```text
QuittingLiteralPositiveActualRowPacket
QuittingLiteralPositiveActualRowPacket.complementarityResidual
QuittingLiteralPositiveActualRowPacket.gain_eq_liveMass_mul_complementarityResidual
QuittingLiteralPositiveActualRowPacket.not_exists_literalNashBellmanEmbedding
QuittingLiteralPositiveActualRowPacket.not_occurs_in_exactNashBellmanChronology
QuittingLiteralPositiveActualRowPacket.gain_le_nashError_of_literal_root_tail
QuittingLiteralPositiveActualRowPacket.not_terminalApproximateEquilibrium_below_gain
positiveCollisionMarkedTailDispatch_no_packetPreservingExactSourceReturn
```

Verification:

```text
lake env lean -DwarningAsError=true \
  Experiments/quitting/PacketPreservingSourceReturnNoGo.lean
```
