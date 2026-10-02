# Independent review: nonnegative-inverse boundary extension

Reviewer: CODEX_TARSKI_PREMIUM. Date: 2026-09-08.

Author-confirmed frozen source:
[NONNEGATIVE_INVERSE_APPROXIMATION_ON_ZERO_DIAGONAL_TABLES](../notes/CODEX_NOETHER_SUPPORT__NONNEGATIVE_INVERSE_APPROXIMATION_ON_ZERO_DIAGONAL_TABLES.md),
SHA `cd4f3064d224e570e8b9c221578af6b96edc10370d01a80a9f44ddaf9547a501`.

Status: **complete mathematical and exact-byte PASS**. All source bytes read.
No repair requested. Ordinary mathematics only; no Lean/build claim or export.
I reconstructed the extension independently before reading this note, and did
not consult NOETHER's review of the original index theorem.

## 1. Claim checked

For an arbitrary signed Fin4 quitting table with Never zero and singleton
matrix Γ_ij=r_i({j})−r_i({i}), the conclusion is actual original-game UE
when det Γ<0 and Γ⁻¹≥0 entrywise. The four own singleton coordinates and
all 44 nonsingleton coordinates remain arbitrary. This strengthens the
strict-inverse theorem by an actual reward-table approximation; it does
not reuse a supplied equilibrium profile or presume preservation of a
particular target under perturbation.

## 2. Independent matrix verification

Write B=Γ⁻¹≥0, K=J−I, and Γ_ε=Γ−εK. For ε||BK||∞<1,

    Γ_ε⁻¹=B+εBKB+ε²BKBKB+... .

The factorization order is correct: Γ_ε=Γ(I−εBK). The series is absolutely
convergent, termwise nonnegative, and supplies an inverse throughout the
segment from 0 to ε. Hence the determinant sign cannot change. Also K has
zero diagonal, so the singleton-matrix diagonal is literally preserved.

The author's second-order positivity argument is valid. If (BKB)_ij=0,
every term B_ik B_lj with k≠l is zero. Nonzero row i and column j therefore
both have the same singleton support {k}. For n≥3, some B_uv>0 has both
u,v≠k: otherwise at least two rows outside k are supported only on column k
and are dependent, contrary to invertibility. Consequently

    B_ik K_ku B_uv K_vk B_kj>0

is a term of (BKBKB)_ij. Thus B+BKB+BKBKB is entrywise positive, including
all entries where both lower-order terms vanish. No positive diagonal of B
or irreducibility premise was silently supplied.

My independent route agrees: KB is irreducible when B≥0 is invertible and
n≥3. A reducibility cut (KB)_(outside C,C)=0 forces every selected column
of B to vanish if the complement has at least two indices; if its complement
has one index, at least two selected columns are supported on that single
row and are dependent. The positive resolvent then gives the same density.
The author's coefficient proof is shorter and also states the precise
second-order boundary mechanism.

## 3. Actual game and all-response closure

The proposed perturbation decreases exactly r_i({j}), i≠j, by ε. It preserves
all own singletons, every nonsingleton, the transition structure, and Never
zero. Its actual gap matrix is Γ_ε and its reward sup-distance is ε.
The original strict-inverse Fin4 theorem applies to each sufficiently small
positive ε without an externally supplied normality premise. Thus there is
no unjustified normality-continuity step in these frozen bytes.

For ANY actual profile p and ANY complete unilateral behavioral response,
the terminal outcome law is the same in both tables. The payoff difference
is at most their reward sup-distance δ, because total finite absorption
mass is at most one. Taking response suprema is legitimate without an
attaining response, and gives

    |B_i^r(p)−B_i^(r')(p)|≤δ,
    |E_r(p)−E_(r')(p)|≤2δ.

This controls the entire behavioral response class, including Never and
arbitrarily late deadlines; no finite-menu approximation of caps is used.
Given η>0, an approximating table within η/4 and one of its terminal
η/2-Nash profiles supply the SAME actual laws with original regret <η.
The two directions of
`quittingGame_exists_uniformEquilibriumPayoff_iff_terminalNash_all_errors`
in `UniformEquilibrium/Quitting/Terminal/TargetTail/TerminalUniformPayoffSelection.lean`
then yield a single original-game uniform-payoff target. This is not an
illicit interchange of independently moving UE targets and accuracies.

## 4. Falsification and exact arithmetic

I independently reproduced the author's displayed rational inverse for
the four-cycle permutation example at ε=1/20. The perturbed determinant
is exactly −129523/160000. The four entries requiring the second-order term
are exactly (0,2),(1,3),(2,0),(3,1). Independent permutation checks in
dimensions 3,4,5 also pass. These are arithmetic tests, not the matrix proof.

The dimension-two warning is correct: any invertible zero-diagonal 2-by-2
matrix has inverse with zero diagonal. Thus there are no strictly positive
inverses anywhere on that slice, even though nonnegative inverse and negative
determinant occur. This refutes a dimension-free density assertion, not
two-player UE existence. The frozen strategic theorem remains Fin4.

The strict theorem is independently accepted in
[my original review](CODEX_FRECHET_CYCLE__INVERSE_POSITIVE_DISCOUNTED_INDEX_ESCAPE__BY_CODEX_TARSKI_PREMIUM.md).
Its bounded coverage and repeated-owner-calendar caveats remain unchanged;
the boundary extension does not establish that every added boundary table
lies outside all previously known classes. The determinant assumption is
not removed, and no arbitrary-finite-game normality reduction is asserted.

Final verdict on the exact SHA above: PASS. No source or export edits made.
