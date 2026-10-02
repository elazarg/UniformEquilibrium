# Conditioned packet reprojection and external anchoring

## Status

Retired from the active question bank.  The acceptable-answer clause below
explicitly allowed a checked decrease of a well-founded source/rank
complexity.  That threshold is met by
`QuittingPositiveMinimumDebtTangentFamily.reducedSupportRankAlternative_of_positiveMinimumDebt`
(`UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/Endpoint/FlatCirculationSupportRankElimination.lean`),
which absorbs flat circulation into strict finite support-rank descent or the
paid-row exit.  The remaining source-reprojection and external-anchor ideas
are retained here as proof-mining context, not as one active indexed question.

## Setting

Let a finite quitting game have player set `I`, reward table `r`, and a
positive-minimum terminal semantic carrier. A reached port `x` stores an actual
semantic source

```text
R(x)=(U_R(x),B_R(x))
```

together with the stopping-law provenance and labelled clock data needed to
execute a frozen atom/reset packet. The budget-stable iteration compiler uses
a canonical candidate annotation

```text
A(x)=(U_A(x),B_A(x)).
```

These two semantic pairs must not be identified without proof.

If `R(x)` is a positive-minimum semantic pair with total debt `D*>0`, then some
coordinate has debt at least `D*/|I|`. Hence `R(x)` cannot satisfy the
compiler's coordinatewise seed bound at any `eta<D*/|I|`. If an artificial
`A(x)` has debt at most `eta` in every coordinate, one direct semantic seam
from `R(x)` to `A(x)` costs at least

```text
D*/|I|-eta
```

in some coordinate. Thus a vanishing direct seam cannot serve as the missing
adapter. This is proved by
`QuittingPositiveMinimumDebtTangentFamily.not_baseDebt_le_of_lt_average`,
`exists_directSeam_ge_average_sub`, and
`exists_totalBlockSeamNat_ge_average_sub`
(`UniformEquilibrium/Diagnostics/Quitting/PositiveMinimumSeedSeamBarrier.lean`).

The remaining producer therefore has two distinct tiers.

## Tier I: actual reached-source packet kernel

Starting from

- a sufficiently late frozen atom/reset packet of mesh `h` anchored at its
  carrier source;
- an actual reached port `x` sufficiently close to that frozen source; and
- the mover, observer, terminal orientation, stopping-law provenance, and
  labelled clock ports carried by the checked packet,

construct one finite literal product-root block and an actual successor port
`y` such that:

1. the block is executable from exactly `R(x)`;
2. the reached terminal source is exactly `R(y)`;
3. the same local kernel can be invoked again at `y`;
4. the mover, observer, terminal orientation, provenance, and two fixed clock
   labels are retained;
5. each retained label contributes at least `kappa*h` of actual marginal Quit
   hazard, for one `kappa>0` independent of the reached source;
6. every port has a positive availability radius `rho`, and the selected
   successor satisfies

   ```text
   rho(y) >= rho(x)-chi(h,delta);
   ```

7. the literal packet data have one uniform payoff/debt bound over all
   selected ports.

This tier has no small-debt seed requirement. In the positive-minimum regime
such a requirement would contradict the barrier above.

The frozen-source core of this tier is now checked on the flat charged-
circulation branch. The theorem
`exists_frozenRadialLiteralFiniteProfilePackets`
(`UniformEquilibrium/Diagnostics/Quitting/Frozen/ActualProfilePacket.lean`)
constructs literal finite root words from the actual frozen radial profile,
retains two fixed active movers with hazard at least a common multiple of the
frontier scale, identifies every internal candidate with the actual reached
semantic pair, and supplies one uniform payoff/debt bound. At the actual
all-Continue successor,
`frozenRadialLiteralPacket_twoLabel_availableConditionedKernel`
(`UniformEquilibrium/Diagnostics/Quitting/Frozen/ConditionedActualProfilePacket.lean`)
identifies both retained live hazards with their exact posterior mixtures and
gives positive two-sided availability when the prior weights are strict and
both component survivals are positive. `abs_frozenRadialReachedWeight_sub_le`
gives the sharp denominator-dependent posterior-loss estimate. These are
conditioning results, not restartability. The subsequent strict-weight and
source-to-inner comparison in
`exists_frozenRadialStrictPackets_available_or_exploitablySourceKilled`
removes component survival as an unclassified premise: every sufficiently
late packet either has the positive-radius conditioned kernel or one original
source marginal has a sure-Quit row before the cutoff and a fixed positive
deviation debt. The latter is not a sure-exit or equilibrium branch. The
remaining Tier-I task is to dispatch that exploitable killed source or select
a different source, and in the available case identify the conditioned
endpoint with the source or replacement chosen at a later frozen rank.

## Tier II: external candidate-anchor adapter or solved-game disjunct

Independently construct one of the following.

### Anchor adapter

For the actual ports and literal root words supplied by Tier I, construct
canonical candidates `A(x)` and exact internal candidate arrays on those same
roots such that:

1. the candidate entrance is exactly `A(x)` and the next canonical candidate
   is exactly `A(y)`;
2. every internal candidate step is an exact terminal-semantic Bellman prefix;
3. prescribed and total two-coordinate candidate endpoint seams are bounded
   by a modulus `omega(h,delta)`;
4. `omega+chi` is operationally sublinear along legal small scales;
5. for every requested accuracy `eta>0`, some legal seed port has
   coordinatewise debt of `A(x_eta)` at most `eta`; and
6. a separate checked all-behavior theorem relates the actual reached
   source/payoff `R(x)` to the artificial candidate anchor `A(x)` without
   asserting a vanishing direct semantic seam.

Item 6 is the substantive adapter. An equality `R(x)=A(x)`, an unproved change
of source, or a direct seam smaller than the positive lower bound is not an
answer. The adapter may use a nonlocal payoff identity, a strategic
continuation argument, or another executable construction, but it must state
exactly how the candidate payoff is implemented from the actual reached source
against arbitrary behavioral deviations.

### Solved-game disjunct

Alternatively, prove that every positive-minimum instance in which the anchor
adapter cannot be constructed already has a uniform-equilibrium payoff by an
independent checked route. Merely assuming the desired payoff as the disjunct
is not a producer theorem.

## Logical scope

Tier I is a local source-matching problem. Tier II is a distinct semantic
implementation problem. Their composition supplies the concrete
`QuittingBudgetStablePacketSystem` data and the explicit small-debt seed used
by
`QuittingBudgetStablePacketSystem.exists_chronologicalDebtShadowingCertificate_of_seed`
(`UniformEquilibrium/Quitting/Debt/Dynamic/BudgetStableCompatiblePacketIteration.lean`).

The target is not `VanishingDebtAtomChronologicalConsumer reward`, which is
already equivalent reward-table by reward-table to existence of a uniform
payoff. Nor may Tier II conceal that capstone inside a field called an adapter.
A satisfactory adapter must retain the concrete reached port, literal roots,
candidate anchor, quantitative error, and all-behavior implementation relation
needed for one invocation or one composable block.

## Checked groundwork

- `exists_executable_positiveIncidence_normalizedReprojectionGerm`
  (`UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticResetReprojectionWindow.lean`)
  supplies an executable reprojection germ with profile provenance.
- `resetFace_globalMinimum_or_surfaceTension_reprojectionCostate`
  (`UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticResetFaceReprojection.lean`)
  retains a reprojection costate in the static dichotomy.
- `QuittingReprojectionDiffuseWindowPacket.exists_concentrated_or_diffuseDeleted`
  (`UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticResetReprojectionDiffuseClockBridge.lean`)
  records the concentrated/diffuse deleted-clock split.
- `QuittingBudgetStablePacketSystem.exists_summableSeamSource_of_seed` and
  `exists_chronologicalDebtShadowingCertificate_of_seed`
  (`UniformEquilibrium/Quitting/Debt/Dynamic/BudgetStableCompatiblePacketIteration.lean`)
  recursively select and flatten supplied anchored packets.
- `QuittingPositiveMinimumDebtTangentFamily.not_baseDebt_le_of_lt_average` and
  `exists_totalBlockSeamNat_ge_average_sub`
  (`UniformEquilibrium/Diagnostics/Quitting/PositiveMinimumSeedSeamBarrier.lean`)
  rule out the one-tier actual-source/small-seed formulation.
- `frozenRadialLiteralPacket_twoLabel_availableConditionedKernel` and
  `abs_frozenRadialReachedWeight_sub_le`
  (`UniformEquilibrium/Diagnostics/Quitting/Frozen/ConditionedActualProfilePacket.lean`)
  give the exact actual-successor posterior kernel, conditional positive
  availability, and sharp posterior loss.

## Not proved

No theorem dispatches the exploitable killed-source alternative or identifies
an available conditioned endpoint with a later frozen source/replacement.
Thus the checked posterior kernel cannot yet be invoked again as a
source-matched packet. The existing results also do not provide an
all-behavior implementation of a low-debt artificial candidate from a
positive-minimum actual source. The budget-stable compiler begins only after
both tiers have been supplied.

## Acceptable answers

The two tiers may be solved independently.

- A positive Tier I answer gives the literal source-matched kernel, retained
  labels, availability estimate, and uniform bound, including a dispatch of
  the killed-source alternative and a proof that the successor can be used at
  the next frozen rank, without claiming a small-debt actual source.
- A positive Tier II answer gives a concrete external anchor adapter with its
  all-behavior implementation theorem, or a nonvacuous solved-game disjunct.
- A partial result counts only if it eliminates one of those named Tier-I
  residuals, supplies one field of the Tier-II implementation whose checked
  composition closes the positive-minimum branch, or decreases an explicit
  well-founded source/rank complexity.
- A negative answer must falsify a universally quantified tier on an actual
  reached-source class satisfying all of its hypotheses, thereby forcing a
  different branch or adapter. A failed algorithm, numerical search, or
  frozen-source-only example is not a falsifier.

## Dependencies

None between the two tiers beyond their displayed common port and root data.
They are intended to be proof-mined independently and then composed through
the checked budget-stable iteration compiler.
