# Historical resolution: the canonical Fin4 support handoff is renewable

## Original question

Starting from a checked
`CanonicalPairMinimumEndpointSupportRankHandoff`, reconstruct a complete next
Fin4 minimum source at the endpoint and orient every recursive child by one
strictly decreasing finite rank.  The construction had to preserve enough
literal provenance to repeat the same minimum-fibre full-replacement step; a
fresh one-time comparison with a newly chosen parent was not sufficient.

## Resolution

This structural question is answered by checked declarations in
`Research/Quitting/FinFourProducerAtlas/`.

- `CanonicalPairMinimumEndpointSupportRankHandoff.nonempty_endpointSourceRegeneration`
  (`CanonicalPairEndpointSourceRegeneration.lean`) reconstructs a complete
  same-residual `FinFourMinimumAtomProducer` at the canonical endpoint from
  the coherent literal endpoint sequence and its retained terminal atom.
- `FinFourRenewableMinimumSourceNode.nonempty_fullReplacementSourceRegeneration`
  (`CanonicalPairFullReplacementSourceRegeneration.lean`) performs the same
  source-faithful reconstruction at each recursive minimum-fibre
  full-replacement child.
- `FinFourRenewableMinimumSourceNode.terminalExit_or_nonempty_supportDescent`
  and `nonempty_renewalTrace`
  (`CanonicalPairRenewableSourceRank.lean`) give an exhaustive next dispatch.
  Only the minimum-fibre no-entry arm recurses, and its positive-debt support
  is a strict subset of the parent's support.
- `canonicalPairRenewableTransition_rank_lt` gives one global natural-valued
  rank.  Its one-use incoming phase cannot be regenerated; thereafter every
  recursive edge strictly decreases positive-debt-support cardinality.
- `CanonicalPairMinimumEndpointSupportRankHandoff.nonempty_renewalCertificate`
  packages endpoint regeneration and the finite renewal trace.

Thus alternative 1 of the original question is established.  The decrease is
renewable rather than a comparison against a newly reset parent.

## Exact remaining boundary

The renewal trace terminates at one of three nonrecursive outputs:

1. positive total tangent slope;
2. flat support entry; or
3. an off-minimum paid first disagreement.

These exits are not automatically uniform-equilibrium payoffs.
`CanonicalPairMinimumEndpointSupportRankHandoff.consume_renewalTerminalExit`
(`CanonicalPairMinimumEndpointRenewal.lean`) shows that any
source-independent consumer can be applied at the terminal descendant, so no
horizontal-seam backward compiler is needed merely to transport a global
conclusion.  The conditional theorem
`exists_uniformEquilibriumPayoff_of_renewalExitConsumers` records the exact
three consumers still required.

Those terminal consumers belong to the active minimum-return and paid-cap
questions.  Absence of a parent-to-child deviation compiler is therefore not
a defect in the now-complete renewable source/rank result, although a local
source-dependent conclusion may still require one.
