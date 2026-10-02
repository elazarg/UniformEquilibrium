# Renewable canonical handoff with a minimum-fibre common-response compiler

## Status

Important ordinary-mathematics result preserved pending full export review and
Lean validation.

The combined PR 76 renewal construction and minimum-fibre common-response
compiler answer the question **Make the canonical Fin4 support handoff
renewable**, in the sense of its first acceptable alternative. They do not
prove Fin4 uniform equilibrium and do not consume the terminal exits of the
renewal trace.

No Lean seal is claimed here. The corrected common-response source had not
been rerun through Lean when supplied.

## Combined result

Starting from a checked canonical-pair minimum-endpoint support handoff, the
construction provides:

1. a complete same-residual `FinFourMinimumAtomProducer` at the literal
   endpoint semantic cluster;
2. a positive finite atom and source-faithful chronology reconstructed from
   the retained literal endpoint profiles and dates;
3. a one-use `origin` phase followed by a `renewed` phase;
4. a global natural-valued phase/support rank whose initial transition
   decreases and whose recursive transitions strictly decrease positive-debt
   support cardinality;
5. reconstruction of every recursive child from the parent's literal
   full-replacement endpoint family; and
6. an exhaustive finite dispatch ending in positive tangent slope, flat
   support entry, or a paid off-minimum first disagreement.

Only the strict-support branch recurses. Thus the construction is renewable:
it cannot reset its rank by introducing a fresh comparison parent.

Schematically,

```text
canonical handoff
  -> complete endpoint minimum source
  -> finite phase/support descent
  -> one of three nonrecursive exits.
```

## Horizontal cap/response control

On every recursive minimum-fibre full-replacement seam, write `S_n` for the
parent source, `T_n` for the full replacement, and `H_n` for their literal half
stopping-law mixture in the mover coordinate.

For every nonmover `i`, one can select an actual behavioral response
`rho_(i,n)` whose regret tends to zero at both `S_n` and `T_n`. Consequently,

```text
(B_i(T_n) - B_i(S_n))
  - (U_i(T_n[i <- rho_(i,n)]) - U_i(S_n[i <- rho_(i,n)]))
  -> 0.
```

The mover's cap is invariant exactly. The proof uses:

- convexity of the cap in the mover's stopping law;
- affinity of prescribed and fixed-response payoffs on the half chord;
- global minimum debt at both limiting endpoints; and
- an approximate actual best response at the half profile.

The mathematical proof of this compiler was checked separately in
`feedback/MINIMUM_FIBER_CAP_RESPONSE_COMPILER_PROOF__BY_CODEX_ROOT.md`.

This is genuine control across the horizontal seam that source-faithful
causalization alone does not provide. It selects a suitable common response;
it does not transport every externally supplied response, and it does not
assert that the cap displacement itself vanishes.

## Why this answers the renewable-handoff question

The first acceptable output of that question asks for a complete next minimum
source, a strict global finite rank below the incoming source, and enough
provenance to iterate the same construction. The phase-tagged regeneration and
support descent provide exactly those data.

The common-response theorem is not the source of the rank. It closes the
separate horizontal cap/response seam identified during review and strengthens
the recursive edges. For reward-level conclusions, the finite trace can be
consumed at its terminal descendant without transporting a source-indexed
claim backward through every seam.

Therefore the honest conclusion is:

```text
canonical Fin4 support handoff is renewably oriented,
but its three terminal exit kinds remain unconsumed.
```

The phrase "fourth requested item" in the compiler packet refers to a subtask
of the renewal work. It is not alternative 4 of the public question, which is
the construction of an actual positive-gap table.

## Remaining gate work

When review capacity permits:

1. verify the exact current PR head and corrected patch;
2. run Lean elaboration and focused builds;
3. adversarially review endpoint source reconstruction and subsequence
   coherence;
4. check the phase/support transition is global and has no constructor back
   to `origin`;
5. verify the exhaustive dispatch at every renewed child; and
6. after those checks, mark the renewable-handoff question answered and move
   attention to the three exit consumers.

## Principal artifacts inspected

- `CanonicalPairEndpointSourceRegeneration.lean`;
- `CanonicalPairFullReplacementSourceRegeneration.lean`;
- `CanonicalPairRenewableSourceRank.lean`;
- `CanonicalPairMinimumEndpointRenewal.lean`;
- `StoppingLawMinimumFiberCommonResponseCompiler.corrected.lean`; and
- `MINIMUM_FIBER_CAP_RESPONSE_COMPILER_PROOF.md`.

This note preserves the combined mathematical milestone; it is not an export
or a formalization claim.
