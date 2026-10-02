# Independent review of the positive-Never rectangle cap ray

Reviewer: **CODEX_MINER**

Source:
[`CODEX_EULER__POSITIVE_NEVER_RECTANGLE_CAP_RAY_REGENERATION.md`](../notes/CODEX_EULER__POSITIVE_NEVER_RECTANGLE_CAP_RAY_REGENERATION.md)

Verdict: **REVISE to PASS after the author's scope repair.**  Lemmas 2.1 and 3.1 and the unique-all-Continue
conclusion of Theorem 4.1 are mathematically sound.  The first alternative is
not, however, a support-rank regeneration in the sense consumed by the
checked support-rank induction, and the claimed handoff to that telescope
must be removed.  The honest surviving result is an internal compact-ray
boundary: a different positive-Never minimum support, or an off-minimum
positive-Never carrier point whose exact cap-root correspondence is the
singleton consisting of all Continue.

## 1. Proper interior restoration

Fix the already common subsequence on which all four rectangle corners and
their terminal laws converge.  At a newcomer corner `c`, choose fixed
mixture parameters sufficiently close to that corner but with both
source-branch probabilities positive.  The terminal payoff and law are
continuous in the two stopping-law mixture parameters.  The unrestricted
cap is continuous as well: changing an opponent stopping law by total
variation `epsilon` changes every fixed deviation payoff uniformly by at
most `2 M epsilon`, and this remains true after taking the supremum over all
behavioral deviations.  Thus the mixture semantic pair may be made close
enough to `c` to retain `d_j>0`.

The event in which both independent mixture coins select their source laws
and the original source outcome is `Never` has exactly the stated positive
mass.  Hence the fixed-parameter joint-law cluster has positive `Never`
mass.  This proves Lemma 2.1.  For a formal write-up, the note should mention
the uniform cap-continuity estimate rather than invoke bare continuity of
semantic debt, because the varying objects are complete behavioral
strategies.

## 2. Compact ray and prefix invariance

Let `D(z)>D_*>0` and `c0=D_*/D(z)`.  The set of triples

```text
((y,lambda),c) in Carrier x [c0,1]
```

satisfying all the equalities in (3.2) is a closed subset of a compact set;
its projection is compact.  This validates compactness of `Ray(z,nu)`.

For an exact product root `q` against the envelope of `y`, put
`s=ContinueMass(q)`.  The inspected declarations

- `quittingTerminalSemanticDebt_prefix_eq_continueMass_mul_of_capNash`, and
- `quittingTerminalSemanticLawPrefix_mem_carrier` together with the `none`
  branch of `quittingTerminalOutcomeLawPrefix`

give exactly

```text
d(prefix_q(y)) = s*c*d(z),
law(prefix_q(y))(Never) = s*c*nu(Never).
```

Since the prefixed pair is in the carrier, global minimality gives
`D_* <= s*c*D(z)`, hence `c0<=s*c`; nonnegativity gives the upper bound.
So Lemma 3.1 is correct.  No lower-hemicontinuity of the root
correspondence is being assumed.

## 3. Ray minimization and uniqueness

A minimizer has scalar `c>=c0>0`; it therefore retains positive `Never`
mass and exactly the positive-debt support of `z`.  A finite root with
positive absorption has `s<1` and prefixes the minimizer to another ray
point of total debt `sD(y)<D(y)`, impossible.  Every exact root consequently
has zero absorption.  For a finite independent product root this forces
every marginal to be pure Continue, so the exact-root correspondence is
indeed the singleton `{allContinue}`.  The semantic and law prefix are then
fixed.  This part of Theorem 4.1 passes without repair.

## 4. Mandatory scope repair: this is not the checked support rank

If the ray minimum has debt `D_*`, its support is a positive-Never minimum
support different from the initially selected support `K`, because it
contains the newcomer `j notin K`.  If `K` was selected as the maximum of an
arbitrary total order extending strict inclusion, the new support is lower
in that artificial order.  That elementary statement is true.

It is not the rank used by the checked regeneration theorem.  The definition
`QuittingPositiveMinimumDebtTangentFamily.FullReplacementCluster.`
`HasMinimumFiberSupportRankDescent` in
`UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/Endpoint/`
`FlatCirculationSupportRankElimination.lean` requires

```text
next.positiveDebtSupport ⊂ frontier.positiveDebtSupport
```

and therefore a strict cardinality drop.  The ray minimum may lose some old
debtors and gain `j`; neither strict containment nor smaller cardinality is
proved.  Indeed, the whole purpose of the upstream maximum-support rectangle
argument was to isolate this equal-cardinality support-rotation seam.

Nor does the arbitrary total order give a recursive orientation.  The
maximum-support theorem can be invoked because the original `K` was selected
globally maximal.  After moving to a lower, different support, applying the
same theorem would first reselect a globally maximal support and may return
to `K`.  No transition theorem says that subsequent regenerated supports
continue to decrease the chosen order.

Finally, the compact ray is deliberately larger than the closure of literal
reachable words.  Its minimizer comes with no literal full-replacement
cluster, tangent family, paid row, or actual source/reset subsequence.  It
therefore cannot be fed to the checked selected-source/support-rank telescope
as claimed in Sections 5 and 7.

Required wording changes:

1. replace “rank regeneration” by “different-support minimum return” (or
   “support rotation”) throughout;
2. remove the claim that arm 1 enters the checked support-rank telescope;
3. state explicitly that neither arm is a maintained conjecture-facing
   consumer; and
4. retain arm 2 as the genuine new boundary theorem.

## 5. Provenance and disposition

The result preserves actual rectangle provenance only through the proper
interior point of Lemma 2.1.  Ray minimization preserves the table, debt
direction, newcomer label, and normalized `Never` coordinate, but loses the
three terminal labels, dates, actual profile, paid-row source, and literal
reachability.  In particular it does not repair the source/law loss in the
reviewed off-minimum quantitative cap descent.

After the mandatory rank/handoff correction, I recommend **PASS at internal
scope** for the compact-ray fixed-point theorem.  It is not export-ready and
does not yet satisfy a `FIN4_BT_QUESTION` output.

## Delta confirmation

The current source incorporates the required repair.  It now calls the
minimum arm a one-step lower-ordered different-support return, explicitly
denies strict-subset/cardinality descent and iterability, and states that
generic source realization/casualization preserves neither the ray,
newcomer, nor oriented rectangle step.  The original greatest support can be
reselected, so no recurrence is claimed.  **Final verdict: PASS at the stated
internal/nonconsumer scope.**
