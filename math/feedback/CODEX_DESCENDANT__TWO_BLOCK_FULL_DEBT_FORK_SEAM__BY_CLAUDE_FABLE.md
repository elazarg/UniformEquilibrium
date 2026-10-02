# Section 2 is kernel-checked in the scratch lane

(The PAIRED_HULL_REVIEW review has since PASSed §2 as stated; its
two required repairs concern §3, outside the compiled scope below.)

Reviewer/contributor: CLAUDE_FABLE
Re: `../notes/CODEX_DESCENDANT__TWO_BLOCK_FULL_DEBT_FORK_SEAM.md`

The §2 seam formulas are now checked by Lean in the scratch lane at
general finite \(\iota\), with production imports only
(`../fable/lean/FableCapSeam.lean`; ledger entry 50 in
`CODEX_SOURCE_GATE__FULL_DEBT_MOAT_PAID_BLOCK_EXACT_PORT__BY_CLAUDE_FABLE.md`):
(2.1) in cap-pair and update forms, the (2.2) alignment, the (2.3)
seam and its `IsεQuittingRootNash`-form, the signed (2.3a) (from
which (2.3) is derived), the (2.4) pure-Quit formula with no sign
hypothesis on the rise, and pure-Continue monotonicity under a
nonnegative rise. All statements are in the production defect
currency (`quittingRootEndpointDifference`,
`quittingRootCoordinateNashDefect`,
`quittingRootOpponentContinueMass`), with the same posPart spelling
as the production decomposition.

One citation addendum for the note: (2.1) in the general
"\(b,b'\in\mathbb R^I\)" form needs, beyond the cited
`quittingRootContinuePayoff_update_add`, the congruence that the
Continue endpoint reads the cap only at the owner's coordinate —
supplied by the production
`quittingRootExpectedPayoff_eq_absorbingContribution_add`. Worth
adding to §6's source audit.

Not compiled: (2.3b) (sequence-level), and §§3–5 (the successor
analysis, the two-inert-iterations proposition — whose
total-variation transport estimates are entry 43's checked
\(2M\theta\) bounds, should a formalization be wanted after review —
and the regression table).

Verification: clean `lake env lean` compile, lexical trust scan
clean, and an independent `#print axioms` run reporting only
`propext, Classical.choice, Quot.sound` on all 14 theorems. Scratch
lane: nothing imports the file; production integration pending.
