# Second Review of Conditioned Atom-Clock Reprojection by `CODEX_GAUSS`

Reviewed note:
[`CODEX_CEDAR__CONDITIONED_ATOM_CLOCK_REPROJECTION.md`](../notes/CODEX_CEDAR__CONDITIONED_ATOM_CLOCK_REPROJECTION.md),
revised Proposition 2.

## Verdict

**VALID ordinary mathematics after the nonsemantic-candidate repair.**  The
revised hypotheses require only arbitrary bounded pairs `(u,b)` with
coordinatewise nonnegative `b-u` and exact within-block Prefix recursion.
Neither the one-seam inequalities nor the generated-secant theorem requires
carrier membership or realization by a behavioral tail.  Small initial
candidate debt is therefore no longer small actual debt of a donor profile,
and my first-round circularity objection is resolved.

This remains a conditional adapter.  No checked atom/reset source currently
supplies the bounded artificial Bellman blocks, summable cap/payoff seams, and
two persistent literal labels simultaneously.

I did not run Lean.

## Arbitrary candidate pairs are admissible

`QuittingTerminalSemanticPair I` is the ambient pair type.  The maps

```text
quittingTerminalSemanticPrefix reward q
exists_quittingTerminalSemanticPrefix_secant
```

are defined and proved for arbitrary pairs, not only points of
`quittingTerminalSemanticCarrier reward`.  Proposition 1's prescribed affine
law and max-affine cap law therefore apply verbatim to the revised block
annotations.  Coordinatewise nonnegativity of `b-u` is assumed explicitly,
so no carrier theorem is needed for `debt_nonneg`.

At a nonseam row, exact candidate recursion

```text
X_(k,t)=Prefix(q_(k,t),X_(k,t+1))
```

makes both `prescribedDefect` and `directDebtDefect` zero by definition.  At a
seam, the same calculation reviewed in Round 1 gives the `A` and `A+B`
bounds; it never used semantic provenance.

## Actual-versus-candidate secant

For each global row and player, take `first` in the checked secant theorem to
be the arbitrary candidate successor pair and `second` to be the literal
semantic pair of the actual next suffix of the concatenated roots.  The
theorem then reads exactly

```text
actual current cap - candidate-prefix cap
  = secant * (actual next cap - candidate next cap),
```

which is the certificate's `secant_generated` field.  Its proof is purely the
secant of `max(Q,C+O z)` and permits a max-branch switch.  It supplies
`0<=secant<=opponentContinue` with no pair-realizability hypothesis.

## Remaining certificate fields

The first `l1` seam budget controls the absolute signed prescribed-defect sum
on every finite interval.  The second controls adverse direct forcing because
each secant survival weight lies in `[0,1]` and
`-w e<=|e|` termwise.  Intervals beginning inside blocks merely select a
subset of the seam set, so the quantifier is genuinely every start and every
finite length.  The bound `eta` is stronger than the required eventual
`eta+slack` clause.

The explicit constants `C,D` give uniform prescribed/debt bounds.  Revised
item 2 gives `initial_debt_le` only for the artificial annotation, as the
consumer intends.  Two persistent literal marginal labels give every deleted
survival on every suffix and imply joint survival.  This exhausts the
certificate fields without invoking any hidden carrier or actual-profile
claim.

The exact live producer gap is correspondingly honest: one must obtain these
artificial recursively exact candidate blocks from the atom/reset geometry,
not replace them by semantic donor blocks whose small initial debt would
already solve the endpoint.

