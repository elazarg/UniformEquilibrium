# Final review of the singleton sign atlas and its exact checker

Reviewer: ATLAS_REVIEW. Verdict: **PASS**. Ordinary mathematical and exact
finite verification; no Lean/build/git commands were run and no tracked files
were edited by this reviewer.

## Exact reviewed artifacts and scope

- Entire `math/notes/CODEX_COORDINATOR__JOINT_RETURN_SINGLETON_TOPOLOGY.md`,
  SHA256 `9a004211adf6db4ee4f03c7069c3f0f447a0dedd29ee57496d34a83f9f96ff67`.
- `math/experiments/CODEX_PARTITION__FIN4_SINGLETON_CELLS_CHECK.py`, SHA256
  `7f9a66a8f084e0c3b08e07f57752f21020d2b652db6176579b5a301bc0496f72`.
  Mathematical review of the changed code covers `check_joint_return_topology`
  and `check_unpointed_residual_atlas`, their shared exact arithmetic helpers,
  and the new opposition-graph check. The unchanged source-case/I2 routines
  elsewhere in this script are outside this mathematical review.

## Conclusions and checks

Sections1–3 retain the exhaustive necessary-sign prerequisite census and its
exact sharpness witnesses. The ten-template counts, equivalence of A and AH,
unique exceptional matching sign orbit, and each negative table entry agree
with the relocated exact checker. The matrix conditions remain distinct from
physical-root, continuation and higher-reward requirements.

Section4 has exactly21 realizable full sign orbits under its stated generic
matrix restrictions. The 28-to26 sign filtering, all five exact impossibility
arguments, their complete pointed-representative list, and the21 integer
witnesses preserve the independently checked proof. The five exclusions use
strict determinant/degree/passive-row inequalities, not numerical failure.
The witnesses satisfy principal nonsingularity, every child condition, negative
columns, a mutually negative pair, strict positive inverse column0, degree+1,
and failure of the negative-chord criterion. Every full inverse entry is also
nonzero. Only rows14,16,19 have a positive directed Hamiltonian four-cycle.

The entire retained Python script passes. I also reran the independent check
that starts from all4096 full sign words rather than the ten templates, and
uses recursive determinants/cofactor inverses rather than the shared
Gauss-Jordan routine. It gives the same 28/26/21 full orbit sets and verifies
all witness/support/child tests exactly.

The added graph code correctly takes transitive closure of reciprocal-
opposition edges, detects the largest strongly connected component, and
excludes opposition Hamiltonian cycles. Its exact result agrees with my
independent closure calculation:

- 13 acyclic rows: 2,3,4,7,9,10,11,12,13,14,17,20,21;
- 7 single-triangle rows: 1,5,8,15,16,18,19;
- sole four-vertex bowtie: row6.

Section5 correctly delegates to the stronger separately reviewed absorption-
path theorem, states bounded completions and a positive lower bound on at
least one own level, and allows nonperiodic behavior/infinite switching.
Its finite balanced-cycle corollary is explicitly supplied by the linked
note's interpolation construction. The deleted finite-cycle proof is therefore
subsumed, not lost. This review checks the citation and scope; the final
compactness/no-path theorem itself has its separate independent reviews.

## Interpretation

The atlas classifies realizable signs of an intersection of existing necessary
matrix restrictions. It does not assert that every magnitude assignment in
one of its21 orbits satisfies those restrictions, or that any orbit contains
a counterexample. The five impossible candidates were not newly excluded UE
reward classes. The graph/atom consequence restricts strategies and still
permits approximate equilibria with a macroscopic absorption date. The final
note preserves all these distinctions and makes no Fin4 solution claim.

Reproduction command from the repository root:

    python math/experiments/CODEX_PARTITION__FIN4_SINGLETON_CELLS_CHECK.py

## Final scope clarification and frontier preface

The final atlas introduction explicitly says diffuse Nash-approximation
sequences and requires a positive own singleton payoff. I verified by inverse
text replacement and hashing that this is the only change from the previously
reviewed atlas bytes. It clarifies the fixed-table scope; Section5 retains the
uniform bounded-completion and positive-lower-bound hypotheses. The checker
bytes are unchanged.

The two new frontier-preface paragraphs in
`math/notes/CODEX_COORDINATOR__FIN4_RESIDUAL_PARTITION.md` also pass a scoped
review: from `The [complete singleton sign atlas]` up to, excluding,
`The exact global target remains`. Their UTF-8 substring SHA256 is
`c386cef6f8000ef22fa580ee1119b8473c62041f8d2047fcd89e0e0f11fb1497`.
The whole frontier file at this review has SHA256
`50dfe0dad83bcce89bb16d516f8a831477ad3f0c355eb43cbd902850273cbd1c`;
this additional approval covers only those two paragraphs, not a re-review
of the whole file. They correctly report21 realizable sign orbits, the13/7/1
opposition split, the bounded-completion atom theorem, arbitrary postponement
of its date, and its nonapplication to positive-gap minimizing sources.
No new UE coverage or conjecture solution is claimed.
