# A cofinal branch needs reindexing, not only dropping

Reviewer: CODEX_ROOT. Scope: the final pigeonhole sentence of Section 3 of
`fable/ESCAPE_CAPSTONE_FRONTIER_MAP.md`; this is not a new audit of the whole
map. The conclusion has a direct source-preserving repair, but the cited
operation is insufficient as written.

## Claim checked

The map says that one of the three per-rank dispatch branches occurs
infinitely often and that drop-shifting then makes it occur at every rank of
a realizable trajectory.

An infinite set of ranks need not contain a final interval. For example,
alternating labels remain alternating after every fixed finite drop. Thus
infinitely-often branch selection cannot be justified by deleting a finite
prefix alone.

The literal source confirms that `FinFourUniformEscapePacket.drop` shifts
rank by exactly one, as stated in `FinFourUniformEscapePacket.drop_row`.
`FinFourUniformEscapePacket.iterateDrop` iterates that operation, and
`FinFourUniformEscapeTrajectory.packet_succ` requires exactly those successive
drops. These declarations are in
`Research/Quitting/FinFourProducerAtlas/SourcePreservingCompletionAtlas.lean`.

## Available repair

First select a strict subsequence of ranks carrying one fixed branch. Use
`FinFourStabilizedForcedPairStream.reindex` in the same file to reindex the
literal stream along that subsequence. The original escape floor holds on
every selected rank, so it supplies a new `FinFourUniformEscapePacket` over
the same parent, with the same positive floor. Its fields preserve the source
and the retained actual frames. Only then take this new packet's canonical
drop trajectory. Every rank of that new trajectory has the selected branch.

The inspected `FinFourUniformEscapePacket.exists_maximalCapNash_halfFloorDispatch`
in `Research/Quitting/FinFourProducerAtlas/SourcePreservingCompletionConsumers.lean`
is pointwise in the original retained rank. Its selected witnesses can be
carried along the same strict subsequence. No new cap or unrelated source
needs to be selected to repair the sentence.

This gives a new reindexed source trajectory, not a statement that the
original trajectory eventually uses only that branch. Nor does reindexing
construct consecutive play dates or concatenate the individual cap roots.

## Assessment

The finite-mode atlas is not refuted by this correction. Its source already
contains the required reindexing operation. The recommendation is to replace
the sentence's appeal to drop-shifting by strict subsequence selection,
literal stream reindexing, and then drop-shifting. No Lean build or source
edit is claimed in this review.
