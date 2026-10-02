# Mathematical review of the producer-atlas delivery and PRs 74/75

Reviewer: CODEX_ROOT

## Claim reviewed

The PRs claim that every `FinFourQuantitativeFullSupportHardResidual` has one
of six source-distinct outputs:

1. a singleton atom in the selected minimum law;
2. a singleton reached during partial same-stage purification;
3. a singleton reached by the subsequent pure-root orbit;
4. a quantitative high-tail escape subsequence;
5. a common-host same-stage monodromy; or
6. a complementary-pair same-stage monodromy.

The delivery folder makes a stronger claim: it describes a concrete recursive
atlas whose canonical endpoint is a uniform payoff or one of two irreducible
leaves (positive Never or causal suffix atom), with a concrete mixed-radix rank
and complete producer-specific no-go packets.

This review concerns the mathematics, not compilation or code quality.

## Sources inspected

- `exists_finFourHardResidual_minimumLaw_causalSuffixAtom` in
  `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticFinFourMinimumLawFiniteAtom.lean`;
- `QuittingMinimumLawCausalSuffixAtom.nonempty_selectedRows` and the selected-row
  mass/tail alternatives in
  `Research/Quitting/NonsingletonMinimumLawLinearTransfer.lean`;
- `quittingLiveWeightedCollisionTransfer_tailEscape_or_exists_endpointGain` in
  `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticLiveWeightedCollisionTransfer.lean`;
- `quittingPartialPurification_then_sameStage_dispatch` in
  `Research/Quitting/SameStageEndpointPurification.lean`;
- the finite orbit and Fin4 geometry declarations in
  `Research/Quitting/SameStageEndpointMonodromy.lean` and
  `Research/Quitting/FinFourSameStageEndpointMonodromy.lean`;
- the final files of PR 75 under
  `Research/Quitting/FinFourProducerAtlas/`;
- the monolithic PR 74 file
  `Research/Quitting/FinFourExhaustiveProducerAtlas.lean`; and
- the mathematical and generic-atlas files in
  `ephemeral/producer_atlas_delivery/`.

## Verdict on the six-leaf theorem

The six-leaf coverage argument is mathematically sound, conditional only on
the named imported Research declarations. Its delicate low-tail step does not
use the invalid implication that a routed endpoint remains near the minimum
fiber.

The chain is as follows.

1. The Fin4 hard residual yields a selected minimum joint semantic/law point
   with positive debt and a positive **finite** terminal atom. Punishment
   normality has already eliminated the generic positive-Never-only arm at
   this stage.
2. If the atom is singleton, the first leaf is immediate. If it is
   nonsingleton, selected causal rows retain its literal source profiles,
   prefix roots, and marked dates.
3. With \(\mu\) the selected law mass and \(D_*\) the minimum debt, the
   frequent/eventual split at \(\mu^2D_*/16\) is exhaustive. The frequent
   branch is the high-tail leaf. In the other branch one actual row has stage
   mass above \(\mu^2/8\) and tail excess below \(\mu^2D_*/16\).
4. Partial purification changes one player's action at that same literal
   date. It preserves the tail exactly and routes the marked coalition with no
   mass loss. It either reaches a singleton within four updates or reaches a
   pure nonsingleton root.
5. From a pure nonsingleton root, every further orbit edge re-applies the same
   collision-versus-low-tail estimate. Thus every edge has a fresh positive
   literal gain floor and retains the same stage-mass floor. Finiteness gives a
   terminal singleton or a closed simple orbit; the Fin4 orbit geometry gives
   common-host or complementary-pair form.

This is a genuine source-preserving finite classification. It is useful
because the high-tail/low-tail selection and every later profile update remain
inside one dependent source chain.

PR 75 is the maintained form. PR 74 contains essentially the same mathematics
in one file; I found no separate mathematical result in PR 74 that survives as
an additional contribution.

## Scope that must remain explicit

The six leaves are not consumers and do not yet form a well-founded recursive
atlas.

- `FinFourProducerCompletionContract` merely assigns one of four names to a
  leaf. It proves no terminal approximation, return, or regeneration theorem.
- A high-tail excursion is compatible with global minimum debt. It is not a
  lower-rank child.
- The monodromy is a horizontal family of same-stage endpoint updates, not an
  executable chronology visiting the cycle vertices in order.
- `every_edge_no_literalExactification` excludes only an exact Nash--Bellman
  embedding that preserves both the displayed root and tail. It does not
  exclude nonlocal repair, source-anchored verticalization, or another
  chronology.
- Giving the three singleton origins one common contract is a sensible target,
  not yet evidence that one consumer works for all three provenance types.

Accordingly, the honest remaining obligations are the four displayed
completion contracts: singleton completion, high-tail completion, common-host
monodromy completion, and complementary-pair monodromy completion.

## Verdict on the delivery folder

The abstract definitions `StrictDescent`, `Atlas`, `Atlas.run`,
`exhaustive_sweep`, and `result_or_reaches_irreducible` are correct generic
well-founded-recursion bookkeeping. The mixed-radix arithmetic is also a valid
rank *once actual source-complete transitions decreasing its digits are
supplied*.

The concrete prose theorem in the delivery folder is not established by that
generic development or by PRs 74/75. In particular:

1. no concrete Fin4 atlas state is instantiated with the proposed rank;
2. no actual producer is proved to decrease one of its semantic digits and
   carry a backward compiler;
3. no complete family of producer-specific no-go records is constructed;
4. the advertised `NeverIrreducible` and `AtomIrreducible` records and their
   concrete coverage theorem are absent; and
5. at the hard-residual interface used by the PRs, a positive finite atom is
   already produced unconditionally, so the advertised positive-Never versus
   finite-atom endpoint is stale.

The delivery is therefore a useful design specification, not a proved
concrete reduction. Calling it a “canonical irreducible Fin4 endpoint” would
overstate its mathematical content.

## Recommendation

Retain PR 75 as a real source-preserving six-leaf producer dispatch, subject to
the separate formalization review. Treat PR 74 as mathematically superseded.
Revise or quarantine the delivery's concrete irreducible-leaf claims until an
actual Fin4 state, descent relation, compilers, and no-go packet are supplied.

The sharp next question is not another local atlas split. It is whether any of
the four completion contracts can be consumed or regenerated with a strict
finite rank while preserving the source data already packaged by PR 75.
