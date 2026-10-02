# Export-gate falsification review of `SHADOW.md`

Reviewer: `CODEX_GATE_FALSIFIER`

## Verdict

**FAIL for export in its present form.**

The three central calculations survive adversarial checking, but the note does
not meet the export gate.  Its strongest new part is a conditional numerical
telescope showing that repeated source-faithful debt creation must be followed
by unbounded cumulative internal debt drain.  That is a useful specification
constraint, not yet a producer, consumer, equivalence, renewable rank, or
counterexample to an exhaustive route.  The stationary construction exposes a
real weakness of the current Lean container, but that weakness is already
stated in the container's docstring and does not satisfy the mathematical
Tier-I requirement in the question.  The all-behavior implementation estimate
is correct but elementary and is adjacent to a stronger checked same-root seam
barrier.

A corrected version belongs in `notes/` and is a good Research formalization
candidate.  It does **not** yet strictly narrow
`questions/FIN4_TWO_TIER_CHRONOLOGICAL_SHADOWING.md` enough to enter `exports/`
under `exports/README.md`.

## Sources checked

I checked the exact fields and consumers in:

- `QuittingBudgetStablePacketData` and
  `QuittingBudgetStablePacketSystem`, in
  `UniformEquilibrium/Quitting/Debt/Dynamic/BudgetStableCompatiblePacketIteration.lean`;
- `IsOperationallySublinearCost`,
  `BudgetedDivergentCostSchedule`, and
  `exists_budgetedDivergentCostSchedule`, in
  `MathUE/SublinearCostSchedule.lean`;
- `quittingRootThenContinuationProfile_stationary`, in
  `UniformEquilibrium/Quitting/Stationary/Root.lean`;
- `quittingTerminalSemanticPair_rootThenContinuation`, in
  `UniformEquilibrium/Quitting/Root/TerminalSemanticPair.lean`;
- the direct seed/seam bounds in
  `UniformEquilibrium/Diagnostics/Quitting/PositiveMinimumSeedSeamBarrier.lean`;
- the already checked stronger same-root artificial-chain obstruction described
  in `formalized/CHRONOLOGICAL_SHADOWING_SEAM_REDUCTION.md`; and
- the exact acceptable partial answers in
  `questions/FIN4_TWO_TIER_CHRONOLOGICAL_SHADOWING.md`.

No paper theorem is involved.

## 1. Universal stationary self-loop: mathematically valid

Let every marginal of `q` be fair Quit/Continue and let

```text
z = SemPair(stationaryProfile(q)).
```

The complete semantic-pair prefix theorem, together with literal stationarity,
gives

```text
z = Prefix(q,z),
```

including unrestricted behavioral cap coordinates.  Thus the proposed
one-point port system satisfies every actual field of
`QuittingBudgetStablePacketSystem`:

- `length=1` is positive;
- the constant candidate has the exact prefix step and entrance anchor;
- both endpoint seams are zero;
- for `0<h<1`, `kappa=1/2` gives
  `(1/2)h <= 1/2`, the exact hazard of either fixed label;
- radius one and zero availability cost give the successor-radius field;
- actual semantic debt is nonnegative;
- if `R=max(1,max |r_i(S)|)`, prescribed values and caps are in `[-R,R]`,
  and debts are in `[0,2R]`, so the common structure bound `2R` works; and
- zero combined cost is operationally sublinear.

I found no reward-table counterexample to this construction; it is uniform in
the table.  In Fin 4, the optional external observations are also correct:
every specified coalition has date-zero probability `1/16`, joint Continue
has probability `1/16`, and deleted-player Continue has probability `1/8`.

Two repairs are nevertheless mandatory:

1. Successor reach and the selected atom are **not fields** of the inspected
   packet-system structure.  They may be listed as extra facts about this
   realization, but not among “all the fields” being verified.
2. The current structure's own docstring already says that actual-source
   provenance may live externally and is not identified with the annotation.
   The construction confirms that design limitation; it does not newly refute
   the textual Tier-I question, which explicitly requires literal
   source-matching to the supplied tangent source and atom.

Therefore the universal inhabitance theorem is worth formalizing as an API
regression/specification test, but is not by itself conjecture-facing export
progress.

## 2. All-behavior implementation inequality: valid but not sharp as claimed

Under the stated hypotheses,

```text
B_i(sigma)-U_i(sigma)
  <= (b_i+beta_i)-(u_i-alpha_i)
  <= eta+alpha_i+beta_i.
```

Summing over Fin 4 and using the actual-profile minimum gives

```text
D_* <= 4 eta + sum_i(alpha_i+beta_i).
```

Both symmetric specializations are correct.  This covers Never, arbitrary
late stopping, random clocks, and any behavioral strategy because `B_i` is
assumed to be the unrestricted behavioral cap; no attainment of its supremum
is used.

The word **sharp** should be deleted unless an equality example satisfying the
full quitting-game hypotheses is supplied.  The algebraic constant is exact,
but the note gives no sharpness test.  The conclusion that vanishing debt and
vanishing implementation errors would yield terminal approximate Nash
profiles is correct.

As a gate matter, this inequality is not enough for export.  It is an
elementary one-sided implementation bound, while the checked seam machinery
already gives a stronger obstruction for an entire artificial exact-root
chain.  The note must identify a named open adapter class excluded by this
strictly more general one-sided version if it is to claim independent frontier
movement.

## 3. Total-debt telescope: valid under all displayed extra hypotheses

For semantic pairs, debt is 1-Lipschitz in the payoff/cap `L1` metric.  Thus
the Fin4 endpoint seam gives

```text
|D(e_n)-D(x_(n+1))| <= 4 omega(h_n).
```

With the additional marked candidate and drift data

```text
D(m_n)-D(x_n) >= c h_n-rho_n,
```

the identity

```text
D(m_n)-D(e_n)
 = [D(m_n)-D(x_n)]
 + [D(x_n)-D(x_(n+1))]
 + [D(x_(n+1))-D(e_n)]
```

and `(a)_+ >= a` prove the displayed estimate.  If each coordinate debt lies
in `[0,M]`, the middle sum is at least `-4M`.  Operational sublinearity yields
a selected positive schedule with nonsummable scales and summable combined
cost.  Nonnegativity of `omega` and `chi` then gives summability of `omega`.
With summable `rho`, the lower bound tends to positive infinity.  Hence

```text
sum_n (D(m_n)-D(e_n))_+ = +infinity.
```

No numerical counterexample exists under those exact assumptions.

The hypotheses are not fields of the current packet system: it supplies
neither `m_n`, the drift inequality, nor `rho`.  They must remain explicit in
the theorem statement.  Also the conclusion is only a cumulative **net
semantic-debt drain inside the blocks**.  Exact Bellman prefixing connects the
candidates, but the proof does not produce:

- prescribed-payoff charge;
- punishment-floor admissibility;
- a return to a common semantic pair or full law;
- a well-founded transition; or
- input to the existing admissible near-return consumer.

Accordingly, “source-matched renewable debt return” and “the only remaining
possibility” overstate the conclusion.  Use “divergent cumulative internal
exact-Bellman debt drain.”

Finally, the contradiction with direct reprojection is along the favorable
schedule selected from operational sublinearity.  The API does not say
`omega(h)=o(h)` pointwise at every small `h`.  Any pointwise sentence must be
replaced by the scheduled aggregate statement, unless a separate pointwise
modulus hypothesis is added.

## 4. Coordinate telescope: inequality valid, rank conclusion invalid

For one fixed coordinate `j`, the same proof gives

```text
sum_(n<N) (d_j(m_n)-d_j(e_n))_+
 >= c sum_(n<N)h_n - sum_(n<N)rho_n
    - M - sum_(n<N)omega(h_n).
```

Thus the cumulative coordinate drain diverges when the chain repeatedly
starts on the same face `d_j(x_n)=0`.

What does **not** follow is that retaining the new coordinate produces a
strict support-rank transition.  Another positive coordinate may disappear at
the same transition.  Numerically, the data

```text
d(x)=(1,0),   d(m)=(1,h),   d(e)=d(next)=(0,h)
```

show the missing inference: the marked zero coordinate enters with no endpoint
seam, but positive-support cardinality stays one.  Exact Bellman structure may
impose further restrictions in a particular source construction, but none is
used in the note's argument.  Therefore item 2 of its purported trichotomy
must be weakened to “exit from the fixed `d_j=0` source class,” unless a
no-other-exit theorem is added.

The telescope itself remains correct and useful after this repair.

## Export relevance assessment

Even after the mathematical wording is repaired, the current result does not
meet item 4 of `exports/README.md`:

- It does not supply either Tier I or Tier II from every entrance object.
- It does not reach the chronological certificate or UE consumer.
- It does not give a renewable rank.
- It does not prove that the tangent entrance cannot produce the richer
  packets; that richer implication remains the desired breakthrough.
- It does not refute an exhaustive route.  It excludes only packet attempts
  additionally satisfying the displayed marked-drift data while lacking the
  forced internal drain.

The stationary theorem is an API-vacuity test, not an answer to the textual
Tier-I question.  The implementation inequality is a local estimate.  The two
telescopes are conditional necessary conditions with no consumer.  This is
exactly the category that the export README excludes as a “local lemma without
a consumer” or a “conditional statement whose source hypothesis remains
open.”

To become exportable, a successor result would need one of these additions:

1. derive the marked-drift hypotheses from every positive-slope/support-entry
   entrance and identify the forced drain with an existing admissible-return
   or renewable-rank consumer;
2. prove an exact impossibility theorem for a precisely stated producer class
   that had been claimed exhaustive; or
3. strengthen the drain to a source-faithful return/rank object and show it is
   sufficient for one tier of the maintained question.

Without one of those additions, the correct gate disposition is to retain the
repaired note internally and not place it in `exports/`.

## Exact required repairs before any later reconsideration

1. Reclassify stationary successor reach and atom mass as external facts, not
   packet-system fields.
2. Replace the claimed logical nonimplication “does not follow” with the exact
   specification statement “is not encoded or produced by the current
   interface and represented entrance data.”
3. Preserve all marked-candidate, drift, summable-residual, fixed-coordinate,
   compatibility, and boundedness hypotheses in the telescope statements.
4. Replace “admissible/renewable return” with “cumulative internal semantic-debt
   drain.”
5. State sublinearity consequences along the selected schedule, not
   pointwise.
6. Remove the unsupported strict support-rank claim.
7. Add exact positive/equality and negative boundary tests for the proposed
   final theorem statements.
8. Add a source/novelty audit against the already checked same-root seam
   obstruction; do not present the elementary implementation bound as a new
   replacement for it.
