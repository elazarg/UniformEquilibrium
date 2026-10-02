# Export-gate review of the Fin4 producer atlas

Reviewer: ATLAS_GATEKEEPER

## Claim reviewed

I reviewed the mathematical content of `../producer_atlas_delivery/` and the
heads of PRs 74 and 75, separately from compilation, API design, and Lean proof
engineering.

The export candidate is the following narrow claim.  Every bounded Fin4 reward
table either has a uniform-equilibrium payoff or produces one of six
source-distinct residuals, all attached to one selected minimum joint-law point
and its literal causal suffix chronology:

1. a singleton atom in the selected minimum law;
2. a singleton reached during bounded same-stage partial purification;
3. a singleton reached at a terminal vertex of the subsequent pure-root orbit;
4. a cofinal quantitative high-tail escape subsequence;
5. a common-host positive same-stage monodromy; or
6. a complementary-pair positive same-stage monodromy.

The stronger delivery claim of a concrete recursive mixed-radix Fin4 atlas
ending in canonical positive-Never or causal-atom irreducibles was reviewed
separately and is not part of the candidate above.

## Exact sources inspected

I inspected the following declarations and their surrounding definitions.

- `uniformPayoff_or_nonempty_finFourQuantitativeFullSupportHardResidual` in the
  checked Fin4 hard-residual reduction imported by PR 75;
- `exists_positive_finiteLawAtom_of_finFourHardResidual_minimum`,
  `finFourHardResidual_minimumLaw_causalSuffixAtom`, and
  `exists_finFourHardResidual_minimumLaw_causalSuffixAtom` in
  `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticFinFourMinimumLawFiniteAtom.lean`;
- `QuittingMinimumLawCausalSuffixAtom` and the generic
  `QuittingMinimumLawNeverOrCausalAtomDispatch` in
  `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticLawCarrierCausalization.lean`;
- `SelectedRows`,
  `QuittingMinimumLawCausalSuffixAtom.nonempty_selectedRows`,
  `SelectedRows.eventually_stageMass_gt_square_div_eight`, and
  `TailEscapeSubsequence` in
  `Research/Quitting/NonsingletonMinimumLawLinearTransfer.lean`;
- `quittingPartialPurification_exists_step`,
  `quittingPartialPurification_exists_total_or_singleton`, and
  `quittingPartialPurification_then_sameStage_dispatch` in
  `Research/Quitting/SameStageEndpointPurification.lean`;
- `quittingPartialPurification_then_finFourSameStage_dispatch` and the Fin4
  period/geometry/mass/gain conclusions in
  `Research/Quitting/FinFourSameStageEndpointMonodromy.lean`;
- `QuittingLiteralPositiveActualRowPacket.not_exists_literalNashBellmanEmbedding`
  and its exact root--tail scope in
  `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticLiteralSourceReturnNoGo.lean`;
- the final PR 75 files
  `Research/Quitting/FinFourProducerAtlas/{Source,Leaves,Coverage,LiteralNoGo}.lean`
  and its aggregator `Research/Quitting/FinFourExhaustiveProducerAtlas.lean`;
- the monolithic PR 74 file of the latter name; and
- `questions/FIN4_EXHAUSTIVE_PRODUCER_ATLAS.md`.

PR 75 is the maintained mathematical form.  PR 74 contains essentially the
same theorem in one file and supplies no additional surviving mathematical
result.

## Freshness and conjecture-facing change

The component declarations already supplied:

- an unconditional positive finite minimum-law atom under the Fin4 hard
  residual;
- source-matched selected rows and their anti-diffusive mass floor; and
- a conditional low-tail partial-purification/monodromy dispatch.

Before PR 75 there was no single theorem proving that their hypotheses can be
met on one source chain and giving an unconditional finite residual family
from arbitrary Fin4 game data.  PR 75 supplies exactly that composition.  Its
new content is the fixed-source high-tail/eventually-low-tail split followed by
the dependent low-tail dispatch.  It therefore changes the named boundary
from a collection of conditional producers to one exhaustive six-leaf normal
form.

This is precisely an accepted first result in
`questions/FIN4_EXHAUSTIVE_PRODUCER_ATLAS.md`: a finite list of natural,
source-carrying residual predicates with a coverage theorem.  It is not merely
a restatement of one existing disjunction.

## Proof and source-provenance audit

Let the selected finite atom have mass

\[
\mu>0,
\qquad
D_*:=D(z_*)>0,
\qquad
\lambda:=\mu^2/8.
\]

The proof has no uncovered case.

1. The Fin4 hard residual selects one minimum joint-law point and one causal
   finite atom at that same point.  Punishment normality has already ruled out
   the generic pure-Never-only alternative.
2. Cardinality one gives the first leaf.  Otherwise the atom is nonsingleton,
   and `nonempty_selectedRows` retains the original realizing profiles, exact
   cap-root stacks, selected dates, prefix-debt convergence, and shifted stage
   masses.
3. The predicate
   \[
   \mu^2D_*/16\leq \operatorname{TailExcess}_n
   \]
   is either frequent or eventually false.  The weak high inequality and
   strict low inequality cover equality exactly.  Intersecting either arm with
   the eventual stage-mass floor does not reselect the source family.
4. The frequent arm is a `TailEscapeSubsequence` with stage mass greater than
   \(\lambda\) and tail excess at least \(\mu^2D_*/16\) at every selected rank.
5. The eventual-low arm selects one literal row with stage mass greater than
   \(\lambda\) and tail excess below
   \(\lambda D_*/2=\mu^2D_*/16\).
   `quittingPartialPurification_then_finFourSameStage_dispatch` applies to that
   exact row.  Partial endpoint purification preserves the tail and routes the
   marked mass without loss.  In at most four updates it reaches a singleton
   or a total pure root.
6. From the total pure root, the finite orbit reaches a singleton or a simple
   cycle.  On Fin4 the cycle has period at most eight and is either common-host
   or contains a complementary pair.  At every cycle offset the literal stage
   mass is at least \(\lambda\), and an actual best-endpoint edge has gain at
   least
   \[
   \lambda D_*/8=\mu^2D_*/64>0.
   \]

The apparent near-minimum issue in the routed-recipient transfer route does
not affect this proof.  PR 75 does not infer recipient transfer or minimum
fiber membership for a routed endpoint.  It uses only the low-tail
same-stage purification theorem, whose hypotheses are supplied at the one
selected row and whose later orbit edges re-use the unchanged tail.

Every leaf retains its required source data.  In particular, a carrier point
is never substituted for an actual profile, a suffix atom is never called
current root absorption, and a horizontal endpoint orbit is never called a
chronology.

## Falsification and boundary tests

I tried to break the claimed exhaustiveness at all seams relevant to the
classification.

- **Never boundary:** the generic minimum-law theorem really has a
  positive-Never arm, but the Fin4 hard-residual theorem separately produces a
  positive finite atom at every selected minimum.  Hence omission of a
  positive-Never leaf is valid only at this hard-residual interface.
- **Atom cardinality:** nonempty finite coalitions split exactly into singleton
  and cardinality greater than one.
- **High/low threshold:** using `\le` on the high side and `<` on the low side
  leaves no equality gap.
- **Stage-mass selection:** the high subsequence and low row are intersected
  with the same eventual `\mu^2/8` floor; the proof does not choose a second
  chronology.
- **Purification mass:** each forced pure endpoint routes the existing root
  coalition and does not lower its stage mass.  A singleton can therefore be
  returned immediately; otherwise the nonsingleton invariant needed for the
  next step remains available.
- **Tail provenance:** all preliminary and orbit updates occur at one date and
  leave the post-date tail fixed.  No limiting-law equality is used as a
  replacement for literal tail equality.
- **Cycle geometry:** the cycle conclusion is only the checked Fin4
  common-host/complementary-pair alternative, not a claim about a terminal SCC
  or a temporal realization.
- **All-behavior semantics:** unrestricted behavioral caps enter through the
  minimum-debt and hard-residual inputs.  The output edges are intentionally
  local best-endpoint data; the theorem does not promote them to terminal
  equilibria against arbitrary behavioral deviations.

I found no mathematical counterexample to the six-leaf coverage statement.

## Actual-data adapter and remaining obligations

The global adapter is
`uniformPayoff_or_nonempty_finFourProducerResidual`: from a Fin4 reward table
and a supplied finite reward bound it returns either a uniform-equilibrium
payoff or one of the six residuals.  Thus the source hypotheses are produced
from arbitrary game data rather than postulated.

The six residuals give four meaningful downstream research obligations:

1. consume or source-faithfully regenerate a singleton source;
2. charge or regenerate the quantitative high-tail escape;
3. nonlocally return or regenerate the common-host monodromy; and
4. nonlocally return or regenerate the complementary-pair monodromy.

The three singleton origins must remain distinct until a common consumer is
proved.  Mapping them to one enum value does not prove that such a consumer
exists.

The local no-go on each monodromy edge is valid and source-matched: a row with
positive literal best-endpoint gain cannot be an exact Nash--Bellman edge
while preserving both its displayed root and displayed tail payoff.  This is
a useful boundary test.  It does not establish that every local or finite
chronological repair is impossible, so it must not be advertised as an
exhaustive nonlocality theorem.

## Delivery-folder overreach

The generic recursion in `../producer_atlas_delivery/` is mathematically
correct conditional bookkeeping: a supplied terminal/descent/no-go
trichotomy and a supplied closing theorem can be iterated by a well-founded
rank.  Its mixed-radix arithmetic is also correct as arithmetic.

It is not a concrete Fin4 atlas theorem.  In particular, the delivery does not
construct:

- an actual Fin4 state carrying the proposed rank digits;
- source-complete transitions decreasing those digits;
- backward compilers for those transitions;
- an exhaustive packet of semantic no-gos with a closing theorem; or
- the advertised concrete `NeverIrreducible` and `AtomIrreducible` endpoints.

The advertised positive-Never versus finite-atom final split is additionally
stale at the hard-residual interface, where a positive finite atom is already
unconditional.  None of the generic recursive-atlas or canonical-irreducible
claims may enter an export packet for PRs 74/75.

## Minimal exportable statement

An export packet may state only the following result, with the six structures
defined self-containedly.

> **Fin4 source-preserving six-leaf producer reduction.**  For every reward
> table on `Fin 4` and every finite bound on its coordinates, either the
> quitting game has a uniform-equilibrium payoff or there exist one selected
> positive minimum joint-law point, one positive finite causal suffix atom at
> that point, and exactly one of the six source-distinct outputs listed in the
> first section.  In the high-tail output the fixed floors are
> `stage mass > mu^2/8` and `tail excess >= mu^2 D_*/16`.  In either monodromy
> output the period is at most eight, every displayed stage mass is at least
> `mu^2/8`, and every displayed best-endpoint edge has gain at least
> `mu^2 D_*/64`.  The monodromy geometry is respectively common-host or
> complementary-pair.

The packet may include the literal root--tail exactification no-go as a scoped
corollary.  It must include the four open completion obligations and the
nonclaims below.

## Required nonclaims

The result does not prove:

- a uniform-equilibrium payoff on any residual leaf;
- terminal approximate Nash profiles;
- a cumulative admissible near-return;
- source-regenerated support or face descent;
- that high-tail excess contradicts global minimum debt;
- that a horizontal monodromy is an executable temporal chronology;
- that one consumer handles all three singleton provenance types;
- that the four completion names are inhabited contracts;
- that the six leaves form a recursively well-founded atlas; or
- either canonical irreducible endpoint claimed by the delivery folder.

## Verdict

**EXPORT in a corrected narrow form.**

The six-leaf theorem is a complete answer to the first finite-coverage outcome
explicitly accepted by `questions/FIN4_EXHAUSTIVE_PRODUCER_ATLAS.md`.  It has a
genuine arbitrary-data adapter, preserves source provenance through the
classification, and strictly replaces several conditional interfaces by one
named finite normal form.  The result should undergo ordinary packet assembly
and retain this review plus the independent CODEX_ROOT review.  PR 75 is the
mathematical source; PR 74 is superseded.  The generic recursive atlas and
canonical irreducible claims are not exportable.
