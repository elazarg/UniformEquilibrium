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


# Actual-head cap box and small repairs

The following independent reviews cover the new source optimization section
and the small-head scope lemma in the consolidated note. Neither is an
export or an additional unrestricted UE class exclusion.

# Independent mathematical review: actual-head cap box

Reviewed `HEAD_BOX_GLOBAL_MINIMUM.md`, SHA256
`9dc161ed7528c3974465c2ed42cca6c1a5bbae8310f5ab572e6acaeab15cd363`.

Verdict: **PASS as an internal source reduction**, subject to its stated actual-head, positive-Never, observer-optimal, ALL-END, strict-global-margin hypotheses. It is not an additional UE class exclusion.

## Nonrealized source and supported head deadlines

The support argument is valid without realization of Y. Write alpha_t for i's finite head atom and V_t for its deadline value against P. The exact affine head map gives

`U_i(Y) = sum_t alpha_t V_t + n_i [e_i(P)+h_i U_i(Q)]`.

Every V_t is at most B_i(P), hence at most B_i(Y). Since Q is observer-optimal, the bracket is `e_i(P)+h_i B_i(Q)`, also at most B_i(Y). Equality U_i(Y)=B_i(Y), together with positive n_i, forces the bracket and every positive-weight finite deadline to equal B_i(Y). Thus whenever n_i<1, both head and endpoint branches attain the cap, proving (2). This weighted-average identity is a useful explicit sentence to retain in the consolidated proof.

The retained-query map is a continuous self-map of the augmented actual closure: finite truncations of the fixed actual P, an empty deadline query, and actual approximants to R give a diagonal realization. The omitted finite head tail has vanishing mass, so the uniform replacement coupling estimate controls B as well as U and e. The original Never coordinate converges to N_i(P)N_i(R). This does not require execution after an infinite head.

## Exact equivalence and objective

Substitution into (3) gives a sum of nonnegative terms. For active head observers both coefficients n_i and 1-n_i are positive, so debt zero forces both endpoint debt zero and b_i=a_i. For never-quitting head observers n_i=1, it forces endpoint debt zero and b_i>=a_i. This proves the full-carrier iff, not merely feasibility of selected perturbations.

Multiplying (5) by s gives the pivot cap scale h_p=s/n_p exactly. Hence (6), global optimality on C_P, and the pivot obstacle are correct. Positivity of n_p is essential and is explicitly assumed.

## Collar and one-zero perturbation

The finite pivot-head conditional payoff W is bounded by M epsilon, because the event that every observer draws head Never has reward zero. Equation (7) and global J_r(Q)>=mu give

`f delta <= epsilon(f M+n_p mu)`.

The denominator is positive when f>0; signs and quantifiers in (8) check. The conclusion excludes only a nonempty pivot-only actual head.

The solo-zero prefix preserves endpoint observer optimality and ALL-END for all sufficiently small positive t: the other three owners have strictly positive continuation caps at t=0, whereas their immediate quit rewards vanish at t=0. Its cap velocities, box condition (9), obstacle derivative (10), and all three rows of (9a) are exact in that small-t regime. If (9) fails, a fixed positive debt coefficient forces t->0 whenever the whole-source observer debts tend to zero; the corresponding gain then vanishes. If (9) holds and D<0, any fixed admissible t gives a fixed strictly positive carrier gain.

The final reviewed bytes correctly state that actual approximant gains converge to `-s t D` and eventually retain half that fixed positive margin. Retain the phrase 'sufficiently small t' when invoking the necessity t->0 from (9a).

No substantive mathematical gap found. No Lean verification claimed.

## Consolidation check: H1--H10 in the root note

The section `Exact global endpoint optimization induced by an actual head`
in `math/notes/CODEX_ROOT__ACTUAL_MINIMUM_AND_MIXED_ENDPOINT.md` passes the
same independent review. The reviewed whole file has SHA256
`d33ac7331e3c2fd665bed9b11fb9982b2ab98c54ae244511f34db5fd5cf05b3f`;
the reviewed section, heading included through its final paragraph, has SHA256
`2854e11cbd5d7a3cc74df84715d5ae2a462816c7dc820a05dc6e56ea8b9d5c07`.
Only this newly consolidated section was reviewed in this pass.

The inserted weighted-average identity explicitly justifies supported head
contacts even when Y is nonrealized. Labels H1--H10 and H9a preserve the
reviewed formulas and hypotheses. The final actual-approximant statement now
correctly retains at least half the fixed positive carrier improvement.
No new mathematical gap is introduced by consolidation.


# Independent review: pinned small-head obstruction

Reviewed `PINNED_SMALL_HEAD_OBSTRUCTION.md`, SHA256
`1cb830f4c9ab7bc2dcd85c3c82457929ab27e05dc6c96145962d97b683686e69`.

**PASS as an internal conditional scope lemma.** No export or Fin4 exclusion
is asserted. Positive N_p(P), together with the other stated head masses,
makes every old-head scale h_i positive.

The exact pinned-head debt identity bounds both endpoint cap displacement
and endpoint debt by a constant times the whole-source observer error.
Writing the inner head prescription as finite atoms plus its Never branch
proves both displayed debt lower bounds. Every finite head deadline has
absolute payoff at most M beta, because it pays own singleton zero if no
opponent has a finite head draw. The positive-cap observer masses are
therefore O(epsilon); the through-head observer response values stay within
O(epsilon) of their pinned caps.

The first-order Never expansion is uniform in the countable head calendar:
the singleton approximation is exact on events with exactly one finite
opponent, and every omitted event needs at least two independently finite
opponents, with probability O(beta^2). The matrix entries on K are correct,
including an observer's own column: that column occurs only for a zero-cap
observer, so Gamma_ii-b_i=0. Nonnegative-kernel triviality gives a strictly
positive minimum norm on the compact nonnegative unit simplex. After the
positive-cap masses are discarded, beta<=C(epsilon+beta^2) proves the claim
by absorption on a fixed sufficiently small neighborhood.

Endpoint cap nonnegativity is needed for the payoff/cap Lipschitz comparison:
B(R)<=M beta cannot create a fixed cap jump above b>=0. Both U and B change
by at most2M beta; joint Never changes by at most beta. The old head map
contracts each relevant coordinate, giving the stated (4M+r)beta objective
bound. This does not use global minimality. The conclusion only concerns
small heads and endpoints satisfying the explicit cone-injectivity condition;
no producer of that condition for arbitrary inherited endpoints is supplied.

## Root-note consolidation check

The section `Uniform obstruction to small repairs with a fully pinned head`
in `math/notes/CODEX_ROOT__ACTUAL_MINIMUM_AND_MIXED_ENDPOINT.md` is exactly
the reviewed lemma after changing its heading and equation label to S1.
The final whole-note SHA256 is
`c40f261286a32fd689c4069f7758b923b60dcd5f3fa11d84c85aece34fd8ee75`;
the new section hash, including its heading, is
`e0d94e41c921b6aa997b824dc0376b260e72724f2d13676e0c904701918c77cc`.
The preceding reviewed H1--H10 section is unchanged. Consolidation PASS.
