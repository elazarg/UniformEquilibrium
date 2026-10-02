# Review of Proposition 6S

Reviewer: `CODEX_EULER`

Verdict: **VALID ordinary mathematics, with the frozen-head scope stated in
the note.**  I found no constant, mixture-law, cap, or witness-retention gap.

## Claim checked

Proposition 6S transports one rank of
`HasQuittingStoppingLawVanishingDebtAtomAlternative` from the original frozen
source through the simultaneous radial face.  If the inner frontier scale is
`h`, the outer weight of active mover `j` is `w_j`, and `a_j=h w_j`, then under

```text
2 K M |I| h <= q/8
```

the same terminal witness, and in the rectangle arm the same pure-time
witness, gives charge `q/2` and error `e+4 M |I| h` at the whole frozen packet.

## Checks

1. **Nested mixture and cross terms.**  The active marginal is an outer
   complete-law mixture of weight `w_j` between the source law and an inner
   complete-law mixture of weight `h` between source and full replacement.
   Two applications of
   `quittingTerminalOutcomeMass_stoppingLawMixture_eq` collapse this, for each
   terminal outcome and fixed environment, to the single mixture of effective
   weight `a_j=h w_j`.  Sequentially changing coordinates then gives
   `|Pr_new(C)-Pr_old(C)| <= sum_j a_j`.  Simultaneous cross terms are not being
   discarded: the telescoping comparison is between successive full product
   profiles and bounds each coordinate switch in its current environment.

2. **Atom constant.**  The signed atom is a terminal-mass difference times
   one reward coordinate.  Source and full-replacement endpoint can each move
   the displayed outcome mass by at most `S=sum_j a_j`; hence the atom changes
   by at most `2 M S`, and its cardinality-weighted version by `2 K M S`.
   This applies verbatim after the common observer pure-time override in the
   rectangle arm.  Overwriting the selected mover at the endpoint merely
   removes that coordinate from the comparison, so retaining the coarser
   bound `S` is safe.

3. **Unrestricted cap and debt.**  Once the observer law is held fixed, the
   one-switch coupling changes the payoff of every fixed behavioral deviation
   by at most `2 M S`.  Taking suprema therefore changes the unrestricted cap
   by at most `2 M S`, not merely a finite-controller cap.  Prescribed payoff
   has the same bound, so observer debt changes by at most `4 M S`.  In the
   rectangle arm the observer override also removes any radial reset on the
   observer coordinate, leaving only opponent-law changes as required.

4. **Decoder thresholds.**  The old prescribed lower bound is `q/2`; after a
   loss at most `q/8` it remains `3q/8`, stronger than the `q/4` required for
   new charge `q/2`.  The old rectangle lower bound is `q/4`; after the same
   loss it is `q/8`, exactly the new requirement.  Since `S<=|I|h`, endpoint
   debt is at most `e+4M|I|h`.

5. **Orientation and provenance.**  The argument retains the same displayed
   terminal, the same selected mover and full replacement, and in the
   rectangle arm the same pure-time response.  Thus the claimed rankwise
   orientation retention is genuine.

## Scope

The proposition is only a terminal-law and semantic-debt estimate at one
frozen head.  It proves neither equality of conditioned hazards nor survival
of the atom at the actually reached residual port.  It does not identify the
observer with the second clock label, stabilize witnesses across ranks, or
provide a restart after the cutoff.  With those limitations, the final claim
that 6R+6S aligns one positive clock mover and the atom on the same literal
frozen simultaneous packet is justified.

## Sources checked

- `Diagnostics/Quitting/Frozen/RadialScaling.lean`:
  `frozenRadialInnerResetStrategy`, `frozenRadialResetProfile`.
- `Diagnostics/Quitting/Frozen/RadialPacketExposure.lean`:
  `frozenRadialPacketProfile_apply`.
- `Diagnostics/Quitting/StoppingLaw/TerminalSemanticStoppingLawDebtConvexity.lean`:
  `quittingTerminalOutcomeMass_stoppingLawMixture_eq`.
- `Diagnostics/Quitting/StoppingLaw/VanishingDebtAtomAlternative.lean`:
  `HasQuittingStoppingLawVanishingDebtAtomAlternative`.
- `Diagnostics/Quitting/TerminalSemanticPositiveSlopeAtom.lean`:
  `quittingTerminalPayoffDifferenceAtom`.

