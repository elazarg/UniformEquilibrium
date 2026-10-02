Historical design record. Frozen source/review artifact; see Research/Pending/README.md.

# Signed affine-row comparison and opposed-orientation boundary

## Status, source and scope

Frozen known-proof implementation drafts, not compiled, applied, axiom-checked
or integrated. This record is an author self-audit, not independent review.
Root remains sole shared editor/compiler/build/Git owner. No shared writes,
Lean/Lake, cache/worktree/snapshot, child agent or math-note edits were used.

The complete source packet was read:
`math/exports/THREE_SURE_MINIMA_REQUIRE_OPPOSED_MEMBERSHIP_REVERSALS.md`,
SHA256 `83ee0a42c89aa0f37a29b74bee059fc6dca8cbda309f9e6806f84bf410bb8297`.
This unit implements its game-independent one-orientation row comparison in
Sections 2–4 and exact affine-envelope regression in Section 5. It does not
implement source Section 1.2's actual worst-table producer, the screened-root
semantic adapter, the original-table contradiction, or the no-reversing-core
product-support counting argument. Those are separate game-semantic consumers.

The coherent-row weak comparison needed by that latter branch IS exposed.
The all-case facade here takes a reversing-row witness and optional row shape,
exactly the source's one-orientation branch; it does not pretend to settle the
opposed-orientation branch or a game with no such row-shape reduction.

## Immutable artifacts and exact bases

1. `001_SIGNED_AFFINE_ROW_COMPARISON.patch`
   SHA `7f25dac018f597efbd58e7653a9fa902b8b26efa0183d935cc2dd254c22d034f`.
   Adds `MathUE/SignedAffineRowComparison.lean`, currently ABSENT.
   Exact source payload SHA:
   `59c81ec403055487ab9d3a616b7b0cc44f70b9b74f0340d4b93d7508cd3f8bf5`.
2. `002_OPPOSED_AFFINE_ROW_REGRESSION.patch`
   SHA `f22c72da73f4db29d2da79c3fce5f5980789cd2bb0782f9bcd18510bfd165582`.
   Adds `MathUE/SignedAffineRowRegression.lean`, currently ABSENT.
   Exact source payload SHA:
   `bc30e24506647e569aa53b47c39c93afa890678b47d61d52b79cfb8cb3cea906`.
3. `AXIOMS_AND_SOURCE_CONSUMERS.lean`
   SHA `f36de6db49364409b6711d5ff90af0b8261abdcf339d1d02530865c15e95f9b3`.
   Two source-facing four-row consumers; all eighteen new theorem axiom sets
   and both consumer axiom sets are requested. It has not been run.

Both target bases are absence; there is no mutation of an existing proof.
The only project mathematics prerequisite is `MathUE/SignedEndpointStretch.lean`,
read completely, current SHA
`701480fb174f7d9e186d27d0697c39ecbac1a4e7dfb593d65c4cb64a5c90d774`.
Mathlib field simplification, real arithmetic, vector notation and finite case
tools supply the remaining narrow imports. No game-semantic import is added.

Apply/check order is 001 then 002 then the local harness. Root-owned named
targets are `MathUE.SignedAffineRowComparison` and
`MathUE.SignedAffineRowRegression`, serialized. Root should subsequently add
the two coherent module imports to the MathUE umbrella, regenerate the
exhaustive axiom inventory and run the applicable trust/import/full gates.
No umbrella or generated inventory was edited by this worker.

## Exact API for the actual-root adapter

All new declarations are in namespace `Math.SignedAffineRows`.
Definitions in `MathUE/SignedAffineRowComparison.lean`:

- `rowValue p a b` is literally p*a+(1-p)*b.
- `reversingNumerator m alpha p` is D=m+2*alpha*(2*p-1).
- `reversingValue m alpha p` is v=D/(1-alpha).
- `comparisonRemainder m alpha p` is the exact printed polynomial R.
- `reselectedProbability m alpha p` is 1-(1-p)*(m/v).

The main APIs retain exactly 0<m<1/2, 0<alpha<m/4, 0<p<1, both old endpoint
bounds in [-2,2], canonical stretched contact equal to m, and per-row shape
(a<0<b) OR (a>=0 and b>=0). They do not infer the source parameter inequalities
from arbitrary contacts. Endpoint zero is represented by the canonical
`signedEndpointGapStretch_zero`, not by the positive signed branch.

- `row_strict_at_reselectedProbability`: if v>m, every such old positive-part
  row at the internally defined p' is strictly below m.
- `reselectedProbability_legal`: in that branch p<p'<1; p>0 therefore gives
  0<p'. The expression is never asserted to be legal outside this branch.
- `row_le_at_originalProbability`: if v<=m, every such positive-part old row
  is at most m at the SAME original probability p.
- `reversing_row_strict_at_originalProbability`: if v<m, EVERY reversing
  old row is strictly below m at that same p.
- `optional_row_strict_of_reversingValue_eq`: if v=m, either optional shape
  (0,c) or (c,0), c>0, has positive-part old row strictly below m at p.
- `exists_sameOrientation_comparison`: arbitrary indexed row family with the
  displayed bounds/contacts/shapes, one reversing row, and one optional row;
  returns ONE legal selected probability before ALL row comparisons, all old
  rows <=m and some strict row. Its conclusion additionally retains the
  branch identities: high branch selects exactly p' and ALL rows are strict;
  low/equality branches select exactly the original p. A finite family is an
  immediate instance; no artificial finiteness or nonemptiness premise is
  introduced for a coordinatewise proof.

No successful hazard, old globality, all-player ties, game/cap certificate or
opposed pair is an input. The actual game adapter must still prove its literal
full-debt row equations (including late finite dates and Never), then supply
the global comparison separately. In weak branches it must establish old
global attainment BEFORE applying old all-player ties.

## Factored scalar proof and edge audit

`comparison_denominators_pos` proves s=1-alpha, D and v are positive; p>0 is
retained as a source hypothesis. `comparison_factorization` is the exact
unconditional polynomial identity

    m*p*s*D - (D-(1-p)*m*s)*(m-2*alpha*p) = alpha*R.

`comparisonRemainder_pos` follows the printed two cases, not a favorable
row-specific inequality. A=2-m-6*p*(1-p) is positive by the square at p=1/2.
For C=(4-3*m)*p+2*m-2>=0 both contributions are nonnegative and m*A>0.
For C<0 the proof derives p<1/2, sets d=1/2-p>0 and uses alpha<m/4 on the
negative p*C term. The printed quadratic lower bound is strictly above
(2*d-1/4)^2. All these identities/sign estimates are explicit in the body.

`reselectedProbability_coherent_bound` clears the positive D in the printed
fractional comparison, using p'*D=D-(1-p)*m*s. For a coherent positive-left
row, the contact gives s*x<=m-2*alpha*p and nonnegative right endpoint gives
p*row(p')<=p'*x. Multiplication by positive s and p' then invokes the exact
factored bound. This is the same proof as the source's p'/p estimate without
an additional division by p. No cap branch is dropped.

For left endpoint zero, the contact forces the right endpoint strictly
positive; p'>p makes its old affine row strictly fall. For reversing rows,
`reversing_row_value` gives the same v, and the exact new row is
m+(1-m/v)*a<m. Taking positive parts preserves strictness because m>0.

At equality, `original_probability_of_reversingValue_eq` proves
p=(2-m)/4 and both p and 1-p exceed m/2. The separate
`optional_positive_gap_strict` proves the positive optional gap is <2 before
concluding strict improvement. It reuses
`signedEndpointGapStretch_eq_self_iff_of_nonneg` for saturation at 2.
Weak coherent comparisons reuse `le_signedEndpointGapStretch` unchanged.
There is no duplicate signed stretch or sign-preservation foundation.

## Literal regression and limitations

In `MathUE/SignedAffineRowRegression.lean`, the old rows are
(98/99,-48/99), (-48/99,98/99), (23/99,23/99), (0,48/99).
The exact new rows under alpha=1/100 are
(1,-1/2), (-1/2,1), (1/4,1/4), (0,1/2).

`opposedRegression_parameters` verifies the source parameter inequalities
at m=1/4, alpha=1/100, p=1/2. `opposedRegression_stretch_and_contact` verifies
every old endpoint bound, every literal stretch and common contact, plus
the two opposed strict orientations. `opposedRegressionEnvelope` is the
literal nested maximum of all four OLD positive-part affine rows.
`opposedRegressionEnvelope_exact_minimum` states its lower bound at EVERY
p in the CLOSED interval [0,1], equality at p=1/2 and 25/99>1/4.
The lower bound uses the two opposite rows' constant sum 50/99; the actual
minimum computation is exact rational arithmetic, not a sampled search.

This is not a positive-gap game, a global-source counterexample or a proof
that the remaining opposed branch can occur at an actual minimum. The source
observes an embedding with zero own singletons would have all Never exact;
this MathUE-only fixture neither reconstructs that game nor claims otherwise.

## Static checks and remaining elaboration risk

Project/canonical declaration searches found no existing row-comparison owner;
the signed endpoint owner is reused instead of copied. All non-import added
code lines are within 100 characters, and prohibited/deprecated conditional
alias scans were clean. Pinned multiplicative cancellation signatures were
inspected: `mul_lt_mul_iff_left₀` cancels a right factor, while
`mul_lt_mul_iff_right₀` cancels a left factor. Explicit nonzero denominators
are supplied to field simplification. No linter option is changed.

Normal-form rewriting, field-simplifier goal shape, nonlinear-arithmetic tactic
elaboration and warning/axiom output remain unchecked. The allowed axiom list
is propext, Quot.sound, Classical.choice only. No source mathematical gap was
found within the requested algebra unit; no compiler or packet-completion
seal is claimed.
