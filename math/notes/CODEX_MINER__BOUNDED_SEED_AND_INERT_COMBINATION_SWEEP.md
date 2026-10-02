# Bounded synthesis sweep: small-debt seed and paid inertness

Author: `CODEX_MINER`

Status: **bounded conjecture-facing sweep complete; no maintained residual
contracted.**  Exactly three nonduplicate combinations were tested.  The
strongest one gives a reviewed exact boundary: finite splicing really does
regenerate actual full-gap paid sources near the strict Fin4 minimum, but the
open exact-all-Continue tube forces their canonical ports to be literally
inert.  The other two combinations fail respectively at the positive-minimum
small-debt seed barrier and at the source-matched fixed-charge/Nash seam.

Audit performed at repository head `26f2261` against the current changed
source tree.

## 1. Candidate A: finite splicing followed by fresh paid-port selection

### Proposed arrow

Start with actual profiles converging semantically to the strict positive
Fin4 minimum.  Move every player's late and Never mass to finite deadlines,
then reapply the actual-profile terminal-gap adapter.  The hope was that
finite support or fresh source provenance would make the regenerated paid
port charged rather than inert.

### Exact test

The ordinary-mathematics theorem in
[`CODEX_EULER__POSITIVE_MINIMUM_FINITE_SPLICE_INERT_BOUNDARY.md`](CODEX_EULER__POSITIVE_MINIMUM_FINITE_SPLICE_INERT_BOUNDARY.md)
was independently checked in
[`feedback/CODEX_EULER__POSITIVE_MINIMUM_FINITE_SPLICE_INERT_BOUNDARY__BY_CODEX_MINER.md`](../feedback/CODEX_EULER__POSITIVE_MINIMUM_FINITE_SPLICE_INERT_BOUNDARY__BY_CODEX_MINER.md).

The checked one-player finite-splice modulus gives an exhaustive finite
subsequence procedure.  Either some stage retains a fixed positive

```text
NeverMass * MaxPairDeletedSurvivalLimit,
```

or all four splices perturb both coordinates of the semantic pair by `o(1)`.
In the second arm the final finite-deadline profiles still converge to the
same strict minimum point and their total debt tends to `D_*>0`.

Fresh paid-port selection at those final profiles does preserve actual
source provenance, but it does not create charge.  Their envelope coordinates
converge to `B_*`, which lies in the open exact-all-Continue tube from
`exists_finFour_strictMinimumPlateau_openDebtHomotopyTube_of_no_uniformPayoff`.
At every canonical prefix depth:

1. `quittingCapLiftedPrefixRoot_exactNash` makes the selected root exact Nash
   against the current envelope;
2. tube uniqueness forces that root to be all Continue; and
3. `quittingTerminalSemanticPrefix_allContinue_eq_self_iff_isZeroNash_at_cap`
   fixes the full semantic pair.

Induction gives zero absorption at every depth, so the complete absorption
series is zero and
`QuittingPaidCapLiftedSource.inertStall_of_totalAbsorption_eq_zero` applies.

### Verdict

**No contraction.**  The failed implication is now exact:

```text
minimum-approaching actual source
+ finite deadlines for every prescribed law
+ freshly selected full-gap paid row and port
  does not imply a charged/noninert canonical port.
```

The complementary positive deleted-clock product remains a possible nonlocal
resource, but no checked theorem turns it into a terminal approximation,
charged return, or finite rank.

## 2. Candidate B: chart-deflated atom ports plus budget-stable iteration

### Proposed arrow

Use Proposition 6AY of
`CODEX_RAMSEY__POSITIVE_ATOM_ROOT_REPAIR_FLOOR.md` to represent one unchanged
actual source/endpoint pair at every smaller declared scale.  Feed those
scale-deflated packets into the checked budget-stable compatible-iteration
compiler, hoping that the same actual source also supplies its arbitrarily
small-debt seed.

### Exact test

The chart change is real and useful locally.  If

```text
P=(1-p)A+pR,
```

then every `0<h<=min(p,1/2)` gives a new latent representation

```text
P=(1-h)A[h]+hR
```

without changing the actual marginal `P`, endpoint `R`, source semantic pair,
terminal atom, or fixed pure-time comparison.  Thus a coordinate radius based
only on one chosen mixture coefficient is not intrinsic.

It does not affect the compiler's independent seed field.  At a positive
global minimum `D_*>0`, reviewed Proposition 6N gives, for every actual
terminal-semantic carrier point `z`, some coordinate

```text
debt_i(z) >= D_*/|I|.
```

Consequently no actual carrier annotation is a coordinatewise seed at
accuracy `D_*/(2|I|)`, and every direct seam to a zero-debt diagonal anchor
has fixed total-coordinate cost at least `D_*/(2|I|)`.  Chart deflation changes
neither side of this inequality because it changes no actual semantic pair.

The current type-checked
`isUniformEquilibriumPayoff_iff_diagonal_mem_terminalSemanticCarrier` also
clarifies the limit of a literal repair: proving that an artificial diagonal
anchor itself belongs to the terminal-semantic carrier would already solve
the uniform-payoff target.  The compatible-iteration route may still use a
noncarrier artificial candidate, but it needs a separate all-behavior
actual-source-to-anchor implementation theorem; none is supplied by the chart
change.

### Verdict

**No contraction.**  Proposition 6AY can help the local availability ledger,
but it cannot populate the small-debt seed or its implementation seam.  The
two compiler tiers remain genuinely independent.

## 3. Candidate C: Nashify the inert paid event with the full-support packet

### Proposed arrow

Use the Fin4 hard residual's quantitatively full-support stationary packet to
put positive mass on the participant action that creates the persistent paid
event of an inert source.  If this could be done against the inert source's
literal cap tail, it would create the missing charged exact Bellman edge.

### Exact test

The proposed root is not source matched.  Near the minimum prescribed-payoff
fiber, the checked linear absorption-defect moat makes all Continue the unique
exact root.  More quantitatively, a fixed-charge root against such a tail has
a fixed positive Nash defect.  The checked
`FinFourCarrierSourceChargeDebtErrorGate` packages the path-level consequence:
an exact carrier-source path containing charge at least `a>0` must start at
debt at least `D_*+eta_a`; an approximate path starting near the minimum must
pay fixed aggregate root error `e_a`.

The accepted full-support/stationary packet lives at a separately produced
actual stationary source.  `FIN4_STATIONARY_PAID_CARRIER_LINEAR_DEBT_MOAT`
already says that a charged exact conversion at its literal prescribed tail
is possible only on the off-minimum side of a fixed debt moat.  No declaration
transports the packet root, its Nash inequalities, or its atom masses to a
minimum-approaching inert source.

The exact local regression
[`CODEX_EULER__FIN4_INERT_PAID_ROW_FULL_REACH_NONCONVERSION.md`](CODEX_EULER__FIN4_INERT_PAID_ROW_FULL_REACH_NONCONVERSION.md)
also shows why paid-row reach is not enough: even unit observer reach and a
unit persistent paid row can coexist with a unique all-Continue cap root,
because the other participant strictly rejects the paid action.  That table
has `D_*=0`, so it is only an interface no-go; the positive-minimum moat above
is the hard-residual obstruction.

### Verdict

**No contraction.**  The missing input is not more mass.  It is one
source-matched theorem controlling the paid-event participants' Nash
inequalities at the inert tail, or a nonlocal off-minimum excursion with a
return/repayment mechanism.

## 4. Strongest exact boundary after the sweep

The two active routes now meet the same obstruction from opposite sides:

```text
actual positive-minimum carrier sources
  cannot be small-debt seeds,

minimum-approaching fresh paid sources
  are eventually literal inert ports,

fixed charged exact roots
  must start a fixed debt distance off the minimum fiber.
```

Therefore no combination tested here bridges the actual-source/small-debt
seed seam or consumes quantitative descent versus inertness.  A genuinely new
arrow must do at least one of:

1. implement a noncarrier artificial small-debt anchor from an actual source
   with an all-behavior theorem whose cost is operationally sublinear;
2. convert the positive `Never * pair-deleted-survival` obstruction into a
   charged return or a finite maintained rank; or
3. align the paid-event participant incentives with one off-minimum charged
   source and return that source to the minimum regime.

Another finite cap, another local atom-retention statement, or reuse of a
separately selected full-support packet cannot supply these arrows.

## 5. Starvation and handoff flags

- `CODEX_EULER__POSITIVE_MINIMUM_FINITE_SPLICE_INERT_BOUNDARY.md` now has an
  independent PASS, but remains internal because it sharpens a no-go rather
  than closing a branch.
- `CODEX_EULER__FIN4_INERT_PAID_ROW_FULL_REACH_NONCONVERSION.md` is a useful
  exact local interface regression and still requests independent review.  It
  should be reviewed so the full-reach dead end is not repeatedly reopened;
  even after review it is likely internal, not an export.
- The current type-checked
  `PositiveJointEndpointUniformPayoff.lean`,
  `PositiveJointExactPrefixOrbitDiagonal.lean`, and
  `UniformPayoffTerminalSemanticCarrier.lean` are mathematically complete
  source results.  Their integration/import status should be completed; the
  first two retire the positive-joint lane only for uniform-payoff existence,
  not for AGKRS classification.

