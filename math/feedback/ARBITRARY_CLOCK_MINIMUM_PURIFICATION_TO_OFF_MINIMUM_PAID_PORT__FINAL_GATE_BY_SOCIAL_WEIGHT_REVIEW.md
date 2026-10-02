# Final gate review of arbitrary-clock minimum purification

Reviewer: `SOCIAL_WEIGHT_REVIEW`

Verdict: **REVISE, with one bounded source-correspondence repair.**  The
mathematical result, constants, arbitrary-support averaging, calendar
classification, strict/equality split, and actual-reach output all pass.  I
found no counterexample.  The packet should not be frozen until the equality
branch cites the checked theorem that actually has the displayed source type.

## What passes

1. For a countably supported stopping law, some positive-support pure time or
   Never point has value at least the prescribed average.  The positive-mass
   deficit proof is valid and uses no cap attainment.
2. Sequential purification needs only literal purity of the already treated
   strategies and convergence of total debt.  Nonmover cap leakage does not
   invalidate that invariant.
3. The strict branch correctly uses
   `Delta = D_*/card I`: every actual target has total debt at least `D_*`, so
   a maximum debtor has this fixed floor.  The scratch actual-reach theorem
   gives gain `Delta/4`, both one-sided reach inequalities, supported source,
   and the joint-reach constant `32 M^2` exactly as stated.
4. The calendar type is complete, including all Never, a date-zero first
   block, and a sole date-zero player.  Against deterministic opponent clocks,
   an unrestricted behavioral response is an average of the finite menu in
   (13)--(14), so the cap is its maximum.  Stabilizing the total
   `none | zero | positive` type therefore gives literal semantic and law
   equality, not merely convergence.
5. The equality branch attains one actual pure-clock global minimum and the
   deadline-rank construction yields an actual off-minimum pure-clock
   descendant.  Choosing a maximum debtor there and applying the same
   actual-reach lemma gives the unified output with `Delta = D_*/card I`.
6. The theorem is an entrance contraction to the named off-minimum paid-port
   waist, not a consumer of that waist; the packet states this boundary
   correctly.  The two review links, question link, source files, formatting,
   and control-character scan all pass.

## Required repair

Section 5 currently says that

```text
finiteClockMinimum_exactCapPurification_or_pureTimeDescentPaidPort
```

directly supplies a literal replacement ancestry from the selected pure-clock
profile `xi`.  Its public conclusion instead starts the recorded chain at

```text
quittingStoppingLawCanonicalizeOn reward xi Finset.univ.
```

and supplies semantic equality with `xi`; it does not itself export a literal
ancestry from `xi` to that canonicalization.  This is not a mathematical
obstruction, because the packet has already selected literal times
`times : I -> Option Nat` with

```text
xi = quittingPureTimeProfileBehavior reward times.
```

The checked theorem with exactly the needed source is

```text
pureTimeMinimum_exists_offMinimumPaidPort
```

in
`UniformEquilibrium/Diagnostics/Quitting/PureTimeMinimumPaidPort.lean`.
Apply it directly to `times`, the global lower bound, and (15).  It returns a
pure-time replacement ancestry from those exact times, an off-minimum target,
an exact pure-time/Never cap response, and its first-disagreement row.  Then
apply the Section 2 maximum-debtor argument to the target as already written.

Accordingly:

- replace the Section 5 invocation of the finite-clock canonicalization
  capstone by the direct pure-time theorem;
- add that declaration and file to Source correspondence; and
- describe `finiteClockMinimum_exactCapPurification_or_pureTimeDescentPaidPort`
  only as the broader finite-clock wrapper or omit it from the proof inputs.

After this exact citation/source-typing repair, I recommend **PASS** with no
further mathematical change.
