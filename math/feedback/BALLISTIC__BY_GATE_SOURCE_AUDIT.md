# Source/freshness audit of `BALLISTIC.md`

## Verdict

**FAIL for export as submitted.**

The weighted-cocycle argument is genuinely new relative to the checked
ballistic omega-chain modules and is mathematically sound after two small but
necessary statement/proof corrections.  It proves a useful algebraic lemma:
an omega chain whose current simplex coordinates stay uniformly interior
forces a fixed point somewhere in the ambient normalized relation.

It does not, however, answer or strictly close a maintained conjecture-facing
question.  Its fixed point has no absolute payoff/root lift or terminal
consumer, and its boundary alternative is only another normalized asymptotic
subbranch.  `questions/FIN4_STRICT_NORMALIZED_INERT_IMPOSSIBILITY_OR_MODEL.md`
explicitly lists another ballistic/complementarity split without consumers as
a nonanswer.

The theorem is worth retaining as an internal algebraic note and likely worth
formalizing opportunistically, but it does not meet the export gate's
adapter-and-consumer/named-boundary requirement.

## Exact checked source correspondence

The relevant checked source is
`Research/Quitting/FinFourProducerAtlas/BallisticNormalizedOmegaChain.lean`.
For one fixed actual strict-ray source:

- `FinFourUniformlyBallisticNormalizedSource` retains full binding, a positive
  renewal-ratio floor `eta`, and the literal cutoff after which it holds;
- `FinFourBallisticNormalizedOmegaChain` retains one common source-window
  extraction;
- `renewal`, `work_nonpos`, and `current_work_eq_zero` give, at every integer
  node, exactly the equations denoted `(R)` and `(C)` in `BALLISTIC.md`; and
- `sourceFiniteWindow_tendsto` retains convergence of complete consecutive
  windows from that same actual ray.

The checked actual-data entrance is
`nonempty_ballisticNormalizedOmegaChain_of_fullBinding_of_eventually_all_currentHazard_pos`
in the same file.  It starts from the source-attached
`FinFourStrictRayForwardExactCapTail`, assumes full limiting binding and
eventual positivity of all current normalized hazards, derives a positive
renewal-ratio floor, and constructs the omega chain.  Thus the candidate's
abstract theorem can be applied to the nonnegative half of a checked omega
chain with

```text
M = flow.analysis.normalized.soloMatrix,
J = flow.analysis.normalized.collisionMatrix.
```

The preceding source production is in
`Research/Quitting/FinFourProducerAtlas/FullBindingPointwiseSupportBallistic.lean`.

`Research/Quitting/FinFourProducerAtlas/BallisticNormalizedOccupation.lean`
adds a balanced occupation measure but does not prove the candidate's fixed-
state theorem.  The exact regression in
`Research/Quitting/BallisticNormalizedSelectedChainRegression.lean` has a
special explicit `fixedState_edge`; it does not prove that every uniformly
interior normalized chain forces some ambient fixed state.  The candidate's
weighted finite-block argument is therefore fresh rather than a duplicate of
that example.

The existing scope is summarized accurately in
`formalized/FIN4_BALLISTIC_NORMALIZED_FLOW_OMEGA_CHAIN_AND_SELECTED_CHAIN_NO_GO.md`:
the source-compatible omega chain carries normalized current hazards, tail
hazards, and renewal ratios, but no absolute product roots, payoff vectors,
Bellman seam, or terminal consumer.

## Mathematical audit of the cocycle proof

After uniform interiority is available, the proof is correct.
Complementarity gives

```text
M Lambda_n + rho_n J lambda_n = 0.
```

Renewal and `rho_n >= eta` give a uniform positive lower bound for every
coordinate of `Lambda_n`.  On a near-return block `[a,b)`, the geometric mean
of `g_n = 1-rho_n` and the cocycle weights

```text
alpha_{n+1} = alpha_n g_n / q
```

indeed give `alpha_b=alpha_a=1`.  Weighted telescoping yields

```text
B = r A + q (Lambda_a - Lambda_b),
M A + J B = 0.
```

After division by `Z`, compactness and `Lambda_a-Lambda_b -> 0` produce an
interior simplex vector `y` and `r in [eta,1]` satisfying

```text
(M + r J) y = 0.
```

That vector gives a genuine fixed state of the *normalized algebraic
relation*.  No probabilistic or behavioral claim is used in this part.

Two corrections are required.

### 1. The alternatives are not exclusive

The statement says “exactly one.”  This is false.  Let `M=J=0`, take the
constant chain `lambda_n=Lambda_n=e_1`, and any constant
`rho in [eta,1]`.  A different coordinate is identically zero, so the boundary
alternative holds.  At the same time every interior `y` and every admissible
`r` satisfy `(M+rJ)y=0`, so the fixed-state alternative also holds.

The correct statement is:

```text
boundary reduction, or interior fixed-state reduction;
more precisely, if the boundary reduction fails, the fixed state exists.
```

### 2. Uniform interiority holds only eventually

Failure of a subsequence tending to zero implies

```text
exists delta>0, exists N, forall n>=N, forall i, lambda_{n,i}>=delta,
```

not the displayed bound for every `n`.  An isolated zero at an early date is
compatible with failure of the boundary alternative.  Discarding the finite
prefix repairs the proof without changing the conclusion.

The near-return pairs `a_k<b_k` should likewise be selected beyond increasing
cutoffs.  Compactness of the simplex supplies such pairs.

## Source attachment and behavioral scope

The checked omega chain is genuinely attached to one actual strict ray by
whole finite-window convergence.  Nevertheless, the new `y` is a weighted
average of normalized omega states.  It is not:

- a state visited by the omega chain;
- a limit of a single coordinate subsequence;
- an actual behavioral profile or terminal-semantic pair;
- an exact product root against an unrestricted behavioral cap; or
- a Nash--Bellman return block.

This is not a hidden strategy-class error: `BALLISTIC.md` mostly states these
limitations correctly.  The theorem itself is purely matrix-algebraic.  The
unrestricted behavioral semantics reside only in the upstream construction of
the strict exact-cap ray; they are not recovered by averaging its normalized
states.

The boundary alternative also does not yet give source support descent.  It
says that one normalized current coordinate tends to zero along omega-chain
indices.  The checked source-window provenance can approximate those states by
actual ray windows, but it does not turn asymptotic smallness into an exact
omitted coordinate, a regenerated minimum source, or a finite-rank edge.

## Relation to maintained questions

The result does not answer
`questions/FIN4_STRICT_NORMALIZED_INERT_IMPOSSIBILITY_OR_MODEL.md`:

- it neither contradicts the strict normalized inert configuration nor
  realizes it as a positive-gap table;
- it supplies no terminal approximation, uniform payoff, admissible return,
  or regenerated finite-rank source; and
- its two outputs still need independent consumers.

It also does not answer `questions/FIN4_MINIMUM_RETURN_CAPSTONE.md` or any of
the three named connection questions in `questions/README.md`.

The genuine narrowing is internal to the normalized ballistic analysis: in
the uniformly interior subcase, existence of an ambient fixed state no longer
needs to be conjectured.  The remaining mathematical obligation is still the
one already isolated by the formalized omega-chain packet: lift a normalized
state to one actual absolute Nash--Bellman object, or use source/maximality
data to exclude it.  Because the maintained question explicitly rejects an
additional ballistic/complementarity reduction without such a consumer, this
is not yet export-level progress.

## Narrow Lean handoff if retained internally

The clean reusable result is dimension-free and should not be packaged with a
Fin4 consumer it does not have.  A suitable theorem shape is:

```text
BallisticNormalizedChain.boundarySubsequence_or_exists_fixedState
```

with conclusion `Or`, not exclusive-or, and with the proof explicitly
discarding a finite prefix before choosing `delta`.  A short Fin4 corollary can
then apply it to `FinFourBallisticNormalizedOmegaChain.state` on nonnegative
integer offsets.  No `A` or `C` claim should be attached to the averaged fixed
state.
