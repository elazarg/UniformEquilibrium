# Whole-packet gate: linear absorption defect in a strict all-Continue basin

Reviewer: `CODEX_EULER`

Packet reviewed:
[`STRICT_ALLCONTINUE_BASIN_LINEAR_ABSORPTION_DEFECT.md`](../exports/STRICT_ALLCONTINUE_BASIN_LINEAR_ABSORPTION_DEFECT.md)

Verdict: **PASS**.  I found no mathematical, source, or export-gate repair.

## Exact statement and proof

The abstract quantifiers are complete: a nonempty finite player type, bounded
finite quitting table, nonempty compact tail set, one uniform strict singleton
gap, and uniqueness of the all-Continue exact product root at every tail in
that set.  The conclusion correctly produces one open neighborhood and one
positive constant uniform over every product root.

The low-absorption calculation checks exactly.  With

```text
a0 = delta/[2(delta+4M)],
```

opponent absorption is at most total absorption, the outsider-Never
decomposition gives

```text
Delta_i <= -delta/2 + O_i(delta/2+2M) <= -delta/4,
```

and the coordinate-defect identity yields

```text
Def >= (delta/4) sum_i q_i >= (delta/4) A(q).
```

This argument does not assume a singleton active support.  The high-absorption
set is nonempty and compact (the all-Quit point has absorption one); uniqueness
excludes a zero of total defect there.  Projecting the closed `Def<=m/2`
bad set along the compact root cube gives the claimed open payoff
neighborhood.  Combining the two branches with
`c=min(delta/4,m/2)` proves the uniform linear estimate.

The epsilon-root conversion has the correct factor `Fintype.card I`, and the
arbitrary-length stack bound is just the sum of the one-row estimates.  The
successor movement constant `2*C` is also correctly propagated.  No
independence between rows or executable-path hypothesis is smuggled into
these sums.

## Probability and behavioral scope

The packet consistently uses independent private Boolean root marginals and
literal one-row absorption.  It distinguishes endpoint/root Nash defect from
unrestricted behavioral equilibrium.  Unrestricted deviation semantics enter
only through the terminal-semantic Fin4 source adapter, not through the
abstract root theorem.  Multiple simultaneously active players, vanishing
absorption, and arbitrary finite stack length are all covered by the stated
proof.

## Adapter, consumer, and narrowing

The checked singleton-minimum adapter
`exists_finFour_strictMinimum_allContinuePlateau_of_no_uniformPayoff` together
with
`minimumTerminalSemantic_exactNash_eq_allContinue_of_strictSingleton`
supplies the abstract hypotheses.  The independently reviewed whole-minimum-
fiber adapter supplies a compact uniform version without being assumed as an
input field.  The consumer is precise: a stack remaining in the strict basin
cannot carry fixed aggregate absorption or Bellman movement while its total
declared root-error budget vanishes.  This strictly sharpens the existing
fixed-positive-incidence moat and exact path rigidity at the named Fin4
boundary; it does not claim to exclude nonlocal incoming tails.

## Boundaries, sources, and Lean handoff

The one-player identity tests the sharp linear mode.  The two-player all-Quit
root shows uniqueness is necessary, and the noncompact one-player family
shows why compact uniform separation cannot be dropped.  The cited diffuse
regressions have collapsing singleton gap and therefore lie outside the
hypotheses.

The named Nash-defect, outsider-Never, continuity, successor-motion, and Fin4
adapter declarations exist in the cited source files and have the orientations
used in the proof.  The source audit accurately identifies the new step as
the scale-uniform low-absorption estimate joined to the checked compact
positive-incidence moat.  The Lean handoff gives a noncircular theorem shape,
dependencies, and finite regressions, and explicitly postpones the reviewed
fiber adapter rather than encoding it as a structure field.

All `exports/README.md` items are satisfied.  The scope section correctly
excludes root production, chronological construction, nonlocal entry,
selected-clock/atom control, paid repayment, and full conjecture closure.

## Delta gate for the successor-linked amendment

Verdict: **REVISE**, with the mathematics of `(P1)`--`(P5)` passing and three
literal packet repairs required.

The bounded shrink, compact collar, head/tail orientation
`V_t=Succ(V_(t+1),q_t)`, and backward admission are all correct.  The proof
never assumes locality of `V_t` before deriving its distance bound.  The
constant

```text
E < c*rho/(4*C*card I)
```

gives displacement `<rho/2`, and its contrapositive is exactly the fixed
excursion toll `(P5)` provided terminal distance remains `<rho/2`.  The
aggregate-error and arbitrary-length quantifiers, adapter/consumer language,
and unchanged mathematical nonclaims all check.

Before the amendment passes as a packet, repair:

1. Delete the duplicated opening `````text`` fence immediately before the
   definition of `a0` in the low-absorption proof.
2. Delete the duplicated opening `````text`` fence immediately before the
   one-player boundary display `A(q)=q`.
3. Update the final approximate-stack nonclaim.  As written it still says the
   approximate-stack conclusion requires every displayed tail to be assumed
   in `N`, which is no longer true for `(P1)`--`(P4)`.  Say instead that the
   free row-family conclusion `(5)` assumes this, while the successor-linked
   conclusion derives it from terminal proximity and `(P3)`.

Also repair the now-stale relative link in the whole-minimum-fiber adapter:
`FIN4_STRICT_MINIMUM_PLATEAU_ISOLATION.md` has moved from `exports/` to
`formalized/`, so the link target must be
`../formalized/FIN4_STRICT_MINIMUM_PLATEAU_ISOLATION.md`.

No mathematical re-review is needed after these four textual/link repairs.

### Final delta recheck

All four repairs are present in the current shared packet.  Each affected
display now has one balanced fence, the row-family and successor-linked
locality scopes are distinguished exactly, and both minimum-fiber references
target the archived formalized packet.  Final delta verdict: **PASS**.
