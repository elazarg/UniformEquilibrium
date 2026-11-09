# Independent review of the consolidated supporting note

Reviewer: CODEX_ONE_ZERO_REPRESENTATION. Ordinary mathematical review; no
Lean execution or tracked edits.

## Exact artifact and decision

Reviewed `math/notes/CODEX_ROOT__ACTUAL_MINIMUM_AND_MIXED_ENDPOINT.md`, SHA256

`a9e53d432c3487c8b47bd4d06fd55b79a31d1b4443ce23d379959374170a4706`.

**Approved as a supporting note.** The augmented head transfer, displayed
finite-clock constraints, and positive-pair incoming-root lemma are sound
in their stated source scope. The note correctly leaves the global
composition/realization problem open. This review does not approve an
export, a new excluded reward-table class, or closure of either selected
source case.

## Proof sources and checks

The augmented-transfer proof was compared with
`REPRESENTATION/AUGMENTED_HEAD_REPRESENTATION.md`, SHA256
`d7f063fa14da86cea163eafa0d8bfbf3c21d25c7e2de842e9a7f295be0fbf290`,
and its independent check `REPRESENTATION/INDEPENDENT_REVIEW.md`, SHA256
`8f81ec6affa611865f0d7aeb9e5d310129a1fe34c1c762322930ceb329803f0e`.
Both paths are relative to `math/.scratch/FIN4_ONE_ZERO_20261109/`.
The canonical source is
`math/notes/CODEX_COORDINATOR__ZERO_OBSERVER_BOUNDARY_REDUCTION.md`,
especially Sections 5 and 7--9, SHA256
`b445d70d36ba8c6187e7657086e6168548c248f0652c51f6e44efeda9c642b19`.

The positive-pair proof was checked directly and compared with
`EXCHANGE/POSITIVE_PAIR_EXACT_INCOMING.md`, SHA256
`b214235dfcfef5822d940bbfe4761febbc1e673c2c54a817294026f546b522af`,
and independent `VARIATION/POSITIVE_PAIR_INCOMING_REVIEW.md`, SHA256
`e941da9ef5141d39171a25b64d39d6bddf1c7c2cc7fb4b92a9675e0c1bb4cc88`.

The operational declarations previously inspected for this review line are
`quittingContinuationBestResponseValue_rootThenContinuation_eq_max` in
`UniformEquilibrium/Quitting/Root/TerminalDebtPrefix.lean` and
`quittingTerminalSemanticPair_rootThenContinuation` in
`UniformEquilibrium/Quitting/Root/TerminalSemanticPair.lean`. Their role is
the literal prefix max-cap/payoff recursion. They are not formal proofs of
the new augmented statements.

### Augmented transfer and clocks

Preservation of the two finite marginal masses and the three first-coalition
masses preserves the entire head Never-response vector. Original marginal
Never masses are preserved separately. Combining these facts with the
canonical preservation of output payoffs and full caps proves equality of
the whole augmented output under a fixed endpoint. No separate preservation
of the head cap is claimed when a tail offer dominates it.

The geometric first-coalition probabilities, both active-owner cap formulas,
the quiet-observer buffer, and the objective formula agree with the reviewed
derivation. The cap formula for the pivot uses the nonnegative endpoint-cap
hypothesis retained in the note's opening source description. ALL-END and
observer contact give exactly the stated equalities/inequalities; absent
clocks correctly remove their vacuous conditions. The preceding-prefix
objective recursion is the nonnegative debt recursion plus multiplicative
original Never. It does not make the endpoint a minimum or permit deletion
of a binding finite prefix.

### Exact positive-pair incoming root

The first-crossing argument is valid. Before the crossing, total activity is
less than delta. The two positive observer caps therefore stay above b/2:
forced Quit is at most M delta, and each selected Continue cap moves by at
most twice M times the current activity. The cumulative movement is less
than b/32. Their strict Quit gaps and positive survival give the displayed
vanishing j/k activity bound from source observer debt.

Both positive singleton and positive participant-pair rewards are needed in
the last-prior-date response calculation. They bound the entire p/i finite
mass, including the last atom, without an error proportional to that atom.
Together with the preceding j/k estimate this makes the entire prior head
vanish. The ALL-END cap-minus-Never inequality then upgrades convergence of
U,e,N to convergence of the full caps, including the two zero caps. Thus the
extracted root has the exact augmented output, not merely its payoff/cap
projection or a weak early-clock limit.

Positive original Never bounds every extracted root coordinate below one.
Continuity and nonnegative debt/END-gap recursions give observer feasibility,
observer root Nash conditions, ALL-END, and positive original Never in the
tail. The lower bound on q_j+q_k follows from the two forced-Quit estimates
when q_j+q_k is at most one half, and is automatic otherwise. The proof
neither requires nor produces nonnegative tail caps or minimizing tail
status.

## Remaining gap and retention scope

The composition caveat is essential and correctly stated. A literal root
extracted from an inherited endpoint cannot simply be scheduled after an
infinite actual head. Finite truncations preserve the semantic composition
limit but may lose the later root's reduction of original Never in the
ordinary early-clock limit. Allowing arbitrary compact prefix limits instead
would admit AllNever as an endpoint while retaining all nonrealization in
the prefix; this does not contradict the actual-head source theorem.

The note therefore has durable supporting value: it gives a fully augmented
finite-clock model and an exact incoming extension at a specified mixed
face, and it identifies the obstruction to combining them into a source
exclusion. A cap-compatible replacement with fixed positive improvement in
the selected source objective, or a realization-preserving reassociation,
is still required. No such global step is claimed or supplied here.
