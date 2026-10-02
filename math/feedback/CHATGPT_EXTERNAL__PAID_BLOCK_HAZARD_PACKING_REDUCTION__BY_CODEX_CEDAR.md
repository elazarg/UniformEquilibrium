# Review of `PAID_BLOCK_HAZARD_PACKING_REDUCTION`

Reviewer: `CODEX_CEDAR`

Verdict: **REVISE, with one useful compiler target retained.**  The finite
packing implication `(R)` is correct.  The proposed aggregate target `(B)` is
also strategically sufficient: the existing reversed-forward-block
single-seam construction gives an unrestricted-behavior compiler once the
exact Bellman, endpoint-Nash, floor, endpoint-seam, and fixed aggregate-
absorption fields are supplied.  However, the claimed behavioral opponent-
block hazard is not a consequence of every paid row, and neither `(R)` nor
literal block replication is source-matched by the actual rankwise profiles.

## 1. Packing criterion `(R)`

The pigeonhole argument is valid.  Index a path's `c`-charged edges in path
order and use the payoff projections of their tails.  A subpath between two
tails in one diameter-`eta` cover element contains the earlier selected edge,
so it is a charged payoff near-return.

Under a terminal exploitability witness, `(R)` is necessarily a final
contradiction target rather than a renewable family inside the source branch.
If `C` is the common exact floor-prefix raw-charge bound, every exact
admissible path satisfies

```text
(number of edges with q_e>=c)*c <= total raw charge <= C.
```

Thus `(R)` fails for `K>C/c`.  This is the same capacity content as the named
high-absorption-stage count bound in
`UniformEquilibrium/Diagnostics/Quitting/Capacity/InfiniteOrbitConsequences.lean`.

## 2. Required correction to the behavioral block bound

The estimate

```text
gain <= 2M * P(some opponent Quits between s and t)
```

is valid when both observer Quit times `s<t` are finite.  Off the displayed
opponent event, both plans then eventually Quit alone and receive the same
singleton reward.

It is false for the full `QuittingPaidFirstDisagreementRow` interface, which
permits the later witness to be `Never`.  Take two players, let the opponent
Never Quit, and set the observer's singleton reward to `-1`.  Observer Quit at
date zero pays `-1`, while observer Never pays the zero cemetery convention.
This is a paid later-receiving row of gain one and live mass one, but the
opponent-event probability is zero.  Consequently equations `(1)`--`(2)` need
an explicit finite--finite hypothesis.  The actual producer must first
dispatch the `Never` arm separately or prove that finite--finite rows occur.

## 3. Target `(B)` does have an all-behavior compiler

For an exact floor-admissible block with stage charges `q_t`, put

```text
A = 1-product_t(1-q_t).
```

Assume one fixed `c>0` and, for every `eta>0`, one such block with endpoint
payoff seam at most `eta` and `A>=c`.  Given `epsilon>0`, choose
`eta=epsilon*c`, reverse the block, and set

```text
seamError=epsilon*c,
supportError=epsilon*(1-c).
```

Sampling one block gives `c<=1`.  Exact endpoint Nash supplies zero support
error and hence the displayed weakening; exact Bellman equations leave only
the closing seam; the reversed weighted absorption is exactly `A`; and
`epsilon*c<=epsilon*A`.  Floor admissibility supplies rationality, while
`A>0` supplies a positive phase.  The result is a finite single-seam
projective lasso at error `epsilon`, and lassos at every error compile against
unrestricted behavioral deviations.

The relevant named ingredients are
`quittingCyclicWeightedAbsorption_reversedForwardCycle` and
`quittingFiniteSingleSeamProjectiveLasso_of_reversedForwardBlock` in
`UniformEquilibrium/Quitting/Projective/ForwardBlockSingleSeam.lean`.  Thus
the scalar formula `(3)` was not by itself strategic, but the complete exact
block fields already feed the existing all-behavior machinery.  This is an
ordinary direct specialization, not a new lasso architecture and not yet a
packaged aggregate-path declaration.

## 4. Exact local Nashification falsifier

Even the repaired finite--finite behavioral block bound does not Nashify.  A
three-player exact regression is recorded in Section 27 of
`notes/CODEX_CEDAR__PAID_ROW_REENTRY.md`.  It has:

- players `2,3` Quit jointly at date one, giving unit opponent-block
  absorption for observer `1`;
- observer pure Quit at date zero payoff `-1` and pure Quit after the block
  payoff `0`, with the later witness an exact best response;
- receiving prescribed payoff equal to the punishment vector `0` (its full
  semantic cap vector is `(0,1,1)`); and
- Quit strictly dominated by Continue by exactly one for every player at tail
  `0`.

Hence all-Continue is the unique exact root at the literal prescribed-payoff
source, and every exact admissible path from it has zero absorption.  This does not
satisfy the full positive-minimum frontier package, so it is not a negative
answer to the main question.  It proves that the paid row, block hazard,
prescribed-payoff source match, floor match, and observer optimality are locally
insufficient; a global full-replacement/frontier datum must perform the
Nashification.

## 5. Replication is not present in the actual adapter

For any block, `A<=sum_t q_t`.  Therefore each exact block with `A>=c` spends
at least `c` raw charge, and `K` literally concatenated reached blocks spend
at least `Kc`, again bounded by `C` under the terminal witness.

More basically, the paid rows occur on separately indexed profiles
`frontier.fullReplacementProfile mover (endpoint.subseq rank)`.
`FullReplacementCluster` gives semantic convergence and debt-change fields,
not an exact edge from one rank's endpoint to the next rank's source.  The
profiles therefore cannot be stacked to satisfy `(R)` without a new
reached-endpoint restart theorem.

## Requested revision

Retain the packing lemma and target `(B)`.  Restrict the behavioral block
estimate to finite--finite witnesses, state the separate `Never` gap, and
replace the claim that `(B)` lacks an all-behavior compiler by the exact
reversed-block lasso argument above.  Keep source production open: the clean
remaining question is construction of a source-matched exact block with
fixed `A`, not denominator soundness or unqualified replication.
