# Review of the renewable canonical Fin4 handoff

## Verdict

**REVISE.  Do not export in its current form.**

The main source-regeneration and well-founded-rank construction is
mathematically sound as an ordinary-mathematics blueprint.  In particular,
the recursive child atom is not an unrelated-law selection: the checked
finite-atom theorem applies to **every supplied minimizing joint-law point**.
The finite origin tag is also an allowed and honest component of the rank in
the dedicated renewable-handoff question.

The note nevertheless overstates its backward compiler.  Source-faithful
causalization transports response differences through the newly attached
cap--Nash prefix.  It does not transport them across the preceding literal
full-replacement update which changes the parent profile into the child
realizing profile.  Thus the claimed compiler "from any child source to the
original canonical source" has an unproved seam at every recursive edge.
This seam is exactly where other players' unrestricted caps can change.

Accordingly, the note is a strong reduction and appears repairable, but it
does not yet meet the question's explicit backward-compiler gate.  Calling it
Output 1 is honest only after that gate is either proved or the required
compiler is reformulated to a precise terminal certificate which really is
preserved across the full-replacement seam.

## Claim reviewed

Starting from

```text
source, returnSource, packet,
handoff : CanonicalPairMinimumEndpointSupportRankHandoff packet
```

the note claims:

1. regeneration of a complete `FinFourMinimumAtomProducer` at the exact
   canonical endpoint law, retaining the literal endpoint profile sequence
   and dates;
2. entry into a source-faithful tangent lane;
3. recursive regeneration in the flat/no-entry/minimum-fibre branch, with
   strict positive-debt-support-cardinality descent;
4. a global natural rank obtained from a one-use origin tag and support
   cardinality;
5. termination at positive slope, support entry, or an off-minimum paid row;
   and
6. a backward response compiler from each regenerated child to the original
   canonical source.

The note explicitly does not claim that the three terminal tangent exits have
already been consumed into a uniform-equilibrium payoff.

## Declarations checked

I reviewed current repository head `a51982b5d337b480cf02144f4943cd9506458cda`
and the following declarations.

- `CanonicalPairMinimumEndpointSupportRankHandoff.endpointPacket_endpoint_tendsto`
  and its source/half analogues in
  `Research/Quitting/FinFourProducerAtlas/CanonicalPairMinimumEndpointSupportRankHandoff.lean`.
- `exists_positive_finiteLawAtom_of_finFourHardResidual_minimum` in
  `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticFinFourMinimumLawFiniteAtom.lean`.
- `nonempty_sourceFaithfulMinimumCausalization`,
  `nonempty_sourceFaithfulMinimumCausalChronology`,
  `QuittingSourceFaithfulMinimumCausalization.responseMenu_transport`, and
  `opponentSurvival_tendsto_one` in
  `Research/Quitting/SourceFaithfulMinimumLawCausalization.lean`.
- `QuittingMinimumLawCausalSuffixAtom` in
  `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticLawCarrierCausalization.lean`.
- `exists_positiveMinimumDebtTangentFamily_of_pair` in
  `UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/PositiveMinimumDebtTangentFamily.lean`.
- `exists_reextractedFrontier_of_minimumFiberEndpoint` and
  `reducedSupportRankAlternative` in the stopping-law endpoint modules.

## What is genuinely new

Three pieces go beyond the checked one-time handoff.

### 1. Exact-law endpoint source regeneration

The canonical endpoint profiles have a fixed marked terminal and a uniform
stage-mass floor.  Joint compactness therefore gives a joint-law cluster
whose semantic projection is the checked endpoint cluster and whose same
terminal coordinate remains positive.  The supplied-profile causalization
can then retain those exact profiles and dates.

This is a real adapter.  It upgrades the endpoint tangent object to a complete
Fin4 minimum source without choosing an unrelated realizing family.

### 2. Recursive exact-law regeneration

For a tangent node's literal full-replacement sequence, joint compactness
again yields a joint-law point whose semantic projection is the checked
full-replacement cluster.  A potentially delicate step is valid:

```text
exists_positive_finiteLawAtom_of_finFourHardResidual_minimum
```

is pointwise in the supplied joint-law point.  It does not merely select some
other law over the same semantic minimum.  Hence, on the minimum-fibre arm,
one can choose a positive terminal coordinate of that exact joint-law limit
and use `nonempty_sourceFaithfulMinimumCausalChronology` without replacing the
literal full-replacement profile family.

### 3. The phase/support rank

With `B = 5`, ranks

```text
terminal  -> 0
tangent   -> B + supportCard
incoming  -> 2*B + incomingSupportCard
```

strictly decrease along the declared transitions.  The initial decrease uses
the one-use origin tag, while all recursive tangent edges use strict support
cardinality.  This is not the old endpoint-versus-half comparison.  It is a
single natural-valued rank on one finite transition type.

The dedicated question explicitly permits a finite source-origin tag with a
proved acyclic transition order.  Thus this rank is not invalid merely
because its first decrease is a lane change.  Once in the tangent lane,
positive debt makes the support nonempty, so at most three strict support
decreases are possible on `Fin 4`.

## Validity of the three proposed adapters

The three listed adapters cover the central source and rank construction,
with one qualification.

1. **Joint compactification and semantic projection:** valid.  Every actual
   joint semantic/law point is in the compact carrier, and uniqueness of
   semantic limits identifies the first projection of a joint cluster.
2. **Initial marked-mass preservation:** valid.  Stage mass is bounded above
   by the complete terminal-law coordinate, so the uniform floor survives in
   the joint limit.  This supplies the strong causalization at the exact
   stored dates.
3. **Tangent extraction refining a supplied sequence:** credible and local.
   Inspection of `exists_positiveMinimumDebtTangentFamily_of_pair` confirms
   that, after its initial arbitrary realizer choice, the proof only takes a
   tail and a strict subsequence.  Parameterizing that initial sequence should
   yield the proposed helper without new game theory.

For recursive children, uniform stage mass is not required.  The pointwise
finite-law atom theorem plus
`nonempty_sourceFaithfulMinimumCausalChronology` legitimately reselects
positive finite-window marks while retaining the exact supplied profiles.

These three adapters do **not**, however, prove the claimed backward compiler.

## Substantive gap: the full-replacement seam

At a recursive tangent edge the child realizing profiles are

```text
f n = node.frontier.fullReplacementProfile mover (endpoint.subseq n).
```

The causalization identity proves, schematically,

```text
responseDifference(prefix(f n))
  = opponentSurvival * responseDifference(f n).
```

It does not prove a relation between `responseDifference(f n)` and the
corresponding response difference at

```text
node.frontier.source (endpoint.subseq n).
```

Those two profiles differ by the mover's complete behavioral strategy.  For
an observer other than the mover, both prescribed payoff and unrestricted cap
can change.  The cap--Nash prefix theorem has no bearing on this horizontal
update.

This is not a merely formal objection.  Even in a two-player subgame, let the
parent have both players Never and compare player `j`'s responses `QuitAt 0`
and Never.  Give `j` reward one only on the simultaneous coalition `{p,j}`
and zero otherwise.  In the parent the response contrast is zero.  After the
full replacement making `p` quit surely at date zero, the same contrast is
one.  Adding any common all-Continue/cap prefix only multiplies the contrast
inside the child; it does not reconstruct the lost parent contrast.  The
example embeds in Fin4 by making the other players passive.  It is not offered
as a positive-minimum counterexample; it falsifies the purported general
transport identity across the replacement seam.

Consequently, composing only the causalization survival factors does not give
a compiler from a descendant exit back to the original canonical source.
The finite product argument begins after each full-replacement seam and skips
the very operation which creates the next base.

## What would repair the result

One of the following precise repairs is needed.

1. Prove an edge-specific compiler across a minimum-fibre full replacement
   for each of the three terminal certificate types.  It need not preserve
   arbitrary response menus, but it must preserve exactly what the eventual
   positive-slope, support-entry, or paid-row consumer uses.
2. Show that no backward transport is actually necessary: formulate the
   terminal consumers as same-reward-table global consumers which act on the
   descendant tangent frontier and directly return a UE/terminal certificate
   for the game.  Then remove the unsupported claim of a source-to-source
   response compiler and state that the global game conclusion, not a parent
   chronology, is what composes backward.
3. Enrich each transition with additional source-attached response data and a
   checked identity controlling the horizontal replacement seam.

The second repair may be the cleanest.  The conditional capstone
`exists_uniformEquilibriumPayoff_of_reducedSupportRankExitConsumers` already
shows that consumers of the three tangent exits can be formulated globally
on the same reward table.  If the dedicated handoff question insists on a
literal backward compiler, however, that requirement cannot be discharged by
this observation alone.

## Is “Output 1” honest?

There are two different numberings in the maintained questions.

- Relative to `questions/FIN4_RENEWABLE_CANONICAL_SUPPORT_HANDOFF.md`, this is
  a plausible construction of alternative 1 **except for the backward
  compiler gap**.  The source regeneration and renewable finite transition
  rank are real.
- Relative to `questions/FIN4_MINIMUM_RETURN_CAPSTONE.md`, it is not Output 1
  (terminal approximants/UE).  At best it targets acceptable answer 3, a
  renewable rank reduction.  The three tangent exits remain producer
  obligations, exactly as the note acknowledges.

The final version should name the dedicated question explicitly and avoid the
bare phrase “Output 1.”  It should also call positive slope, support entry,
and paid row **terminal atlas exits**, not terminal game outputs.

## Export-gate conclusion

The core source-faithful regeneration and phase/support-rank theorem is
important and likely formalizable.  The complete stated packet does not pass
the export gate because one required field—the backward compiler—is not
proved, and the note currently says that it is.  Revise the theorem to either
supply the horizontal seam or weaken the conclusion to the exact atlas
contraction actually established.  After that revision and an independent
second check of the supplied-sequence tangent extractor, the result should be
reconsidered for export.
